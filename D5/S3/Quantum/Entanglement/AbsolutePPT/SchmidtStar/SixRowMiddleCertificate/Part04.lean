/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part04
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0098 : List (List (List (List ℕ))) :=
  [[[[30886379,185727958,139347179],[12293099,148541398,120753899]],[[49479659,222914518,157940459],[30886379,185727958,139347179]]],[[[58544406,364999212,275466006],[20776806,289464012,237698406]],[[96312006,440534412,313233606],[58544406,364999212,275466006]]],[[[27478469,178912138,135939269],[8304149,140563498,116764949]],[[46652789,217260778,155113589],[27478469,178912138,135939269]]]]

private theorem identity_0098 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(8304149 / 247910400 : ℝ)) =
      tensor4 coefficients_0098 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0098, p_coupled] <;> ring

private theorem negative_0098 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0098 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0098] at hp
  linarith only [hp]

private def coefficients_0099 : List (List (List (List ℕ))) :=
  [[[[77960892626413,28204283704813],[63033909949933,13277301028333]],[[153789359156186,54276141312986],[123935393803226,24422175960026]],[[68831443400173,19074834478573],[53904460723693,4147851802093]]],[[[311343250200500,112983197669300],[251602000336820,53241947805620]],[[613188160499560,216468055437160],[493705660772200,96985555709800]],[[273950527911860,75590475380660],[214209278048180,15849225516980]]],[[[466214027275150,169671292017550],[376554628055950,80011892798350]],[[916732351305500,323646880790300],[737413552867100,144328082351900]],[[408817001884750,112274266627150],[319157602665550,22614867407950]]],[[[310241947660500,113210199052500],[250438957648500,53407209040500]],[[609057816351000,214994319135000],[489451836327000,95388339111000]],[[271108279042500,74076530434500],[211305289030500,14273540422500]]],[[[77410274551875,28317817591875],[62452416571875,13359959611875]],[[151724259573750,53539345653750],[121808543613750,23623629693750]],[[67410358261875,18317901301875],[52452500281875,3360043321875]]]]

private theorem identity_0099 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(597341035 / 18052284416 : ℝ)) =
      tensor4 coefficients_0099 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0099, p_headbox] <;> ring

private theorem negative_0099 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0099 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0099] at hp
  linarith only [hp]

private def coefficients_0100 : List (List (List (List ℕ))) :=
  [[[[101164027,450238454,333580027],[26790907,301492214,259206907]],[[138350587,524611574,370766587],[63977467,375865334,296393467]]],[[[195290310,886401420,660122310],[45381990,586584780,510213990]],[[270244470,1036309740,735076470],[120336150,736493100,585168150]]],[[[93946725,435803850,326362725],[18411525,284733450,250827525]],[[131714325,511339050,364130325],[56179125,360268650,288595125]]]]

private theorem identity_0100 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(81829 / 4407296 : ℝ)) =
      tensor4 coefficients_0100 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0100, p_coupled] <;> ring

private theorem negative_0100 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0100 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0100] at hp
  linarith only [hp]

private theorem node_0111 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0099 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0100 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0101 : List (List (List (List ℕ))) :=
  [[[[38924838063923,14378609583923],[31445909073923,6899680593923]],[[76301531362846,27209074402846],[61343673382846,12251216422846]],[[33924879918923,9378651438923],[26445950928923,1899722448923]]],[[[155398927529192,57544973993192],[125468990615192,27615037079192]],[[304125736423384,108417829351384],[244265862595384,48557955523384]],[[134966096678192,37112143142192],[105036159764192,7182206228192]]],[[[232622670006488,86337064681688],[187707644672888,41422039348088]],[[454520250940576,161949040290976],[364690200273376,72118989623776]],[[201326167685288,55040562360488],[156411142351688,10125537026888]]],[[[154747939468992,57553675507392],[124791978354432,27597714392832]],[[301869483739104,107480955815904],[241957561509984,47569033586784]],[[133453600900512,36259336938912],[103497639785952,6303375824352]]],[[[38599357223992,14382973531192],[31107413519032,6891029826232]],[[75173434451504,26740667065904],[60189547041584,11756779655984]],[[33168648270712,8952264577912],[25676704565752,1460320872952]]]]

private theorem identity_0101 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(182540109119 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0101 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0101, p_headbox] <;> ring

private theorem negative_0101 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0101 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0101] at hp
  linarith only [hp]

private def coefficients_0102 : List (List (List (List ℕ))) :=
  [[[[49157987,222271174,165365987],[11390387,146735974,127598387]],[[68041787,260038774,184249787],[30274187,184503574,146482187]]],[[[94617544,437145488,327033544],[18501304,284913008,250917304]],[[132675664,513261728,365091664],[56559424,361029248,288975424]]],[[[45369778,214694756,161577778],[7021138,137997476,123229138]],[[64544098,253043396,180752098],[26195458,176346116,142403458]]]]

private theorem identity_0102 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(3510569 / 247910400 : ℝ)) =
      tensor4 coefficients_0102 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0102, p_coupled] <;> ring

private theorem negative_0102 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0102 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0102] at hp
  linarith only [hp]

private theorem node_0112 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0101 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0102 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0110 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 32 : ℝ)
  · exact node_0111 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0112 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0103 : List (List (List (List ℕ))) :=
  [[[[50932259,156094918,101289059],[32338979,118908358,82695779]],[[69525539,193281478,119882339],[50932259,156094918,101289059]]],[[[98055126,304571052,198768726],[60287526,229035852,161001126]],[[135822726,380106252,236536326],[98055126,304571052,198768726]]],[[[46943309,148117018,97300109],[27768989,109768378,78125789]],[[66117629,186465658,116474429],[46943309,148117018,97300109]]]]

private theorem identity_0103 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(27768989 / 247910400 : ℝ)) =
      tensor4 coefficients_0103 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0103, p_coupled] <;> ring

private theorem negative_0103 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0103 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0103] at hp
  linarith only [hp]

private theorem node_0109 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0110 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0103 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0108 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0098 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0109 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0104 : List (List (List (List ℕ))) :=
  [[[[49479659,222914518,157940459],[12293099,148541398,120753899]],[[68072939,260101078,176533739],[30886379,185727958,139347179]]],[[[96312006,440534412,313233606],[20776806,289464012,237698406]],[[134079606,516069612,351001206],[58544406,364999212,275466006]]],[[[46652789,217260778,155113589],[8304149,140563498,116764949]],[[65827109,255609418,174287909],[27478469,178912138,135939269]]]]

private theorem identity_0104 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(8304149 / 247910400 : ℝ)) =
      tensor4 coefficients_0104 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0104, p_coupled] <;> ring

private theorem negative_0104 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0104 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0104] at hp
  linarith only [hp]

private theorem node_0107 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0108 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0104 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0105 : List (List (List (List ℕ))) :=
  [[[[14826251,91630102,69056651],[5239091,72455782,59469491]],[[24413411,110804422,78643811],[14826251,91630102,69056651]]],[[[27858768,179672736,136319568],[8393928,140743056,116854728]],[[47323608,218602416,155784408],[27858768,179672736,136319568]]],[[[12942738,87863076,67173138],[3065058,68107716,57295458]],[[22820418,107618436,77050818],[12942738,87863076,67173138]]]]

private theorem identity_0105 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(170281 / 6886400 : ℝ)) =
      tensor4 coefficients_0105 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0105, p_coupled] <;> ring

private theorem negative_0105 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0105 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0105] at hp
  linarith only [hp]

private def coefficients_0106 : List (List (List (List ℕ))) :=
  [[[[77683449848429,29250682462829],[62699562438509,14266795052909]],[[151316339703898,54450804932698],[121348564884058,24483030112858]],[[66822031941869,18389264556269],[51838144531949,3405377146349]]],[[[310032778247668,116959167086068],[250073601197428,56999990035828]],[[602913866949416,216766644626216],[482995512848936,96848290525736]],[[265730112132148,72656500970548],[205770935081908,12697323920308]]],[[[463947625539358,175321165174558],[373975810408798,85349350043998]],[[900748375489436,323495454759836],[720804745228316,143551824498716]],[[396212653961278,107586193596478],[306240838830718,17614378465918]]],[[[308530761674980,116767604887780],[248529102466180,56765945678980]],[[598020613039160,214494299464760],[478017294621560,94490981047160]],[[262523157440980,70760000653780],[202521498232180,10758341444980]]],[[[76932461127299,29154920928899],[61927327408739,14149787210339]],[[148869757980118,53314677583318],[118859490542998,23304410146198]],[[65218580262419,17441040064019],[50213446543859,2435906345459]]]]

private theorem identity_0106 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(2435906345459 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0106 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0106, p_headbox] <;> ring

private theorem negative_0106 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0106 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0106] at hp
  linarith only [hp]

private def coefficients_0107 : List (List (List (List ℕ))) :=
  [[[[95288363,438487126,327704363],[18591083,285092566,251007083]],[[133637003,515184406,366053003],[56939723,361789846,289355723]]],[[[182820750,861462300,647652750],[28264110,552349020,493096110]],[[260099070,1016018940,724931070],[105542430,706905660,570374430]]],[[[87352829,422616058,319768829],[9493469,266897338,241909469]],[[126282509,500475418,358698509],[48423149,344756698,280839149]]]]

private theorem identity_0107 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(9493469 / 991641600 : ℝ)) =
      tensor4 coefficients_0107 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0107, p_coupled] <;> ring

private theorem negative_0107 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0107 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0107] at hp
  linarith only [hp]

private theorem node_0117 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0106 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0107 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0108 : List (List (List (List ℕ))) :=
  [[[[38731203865787,14842433766587],[31228637006507,7339866907307]],[[74964825594334,27187285395934],[59959691875774,12182151677374]],[[32874263433347,8985493334147],[25371696574067,1482926474867]]],[[[154524356880256,59295774480256],[124504651610416,29276069210416]],[[298588511817992,108131347017992],[238549101278312,48091936478312]],[[130672635537736,35444053137736],[100652930267896,5424347867896]]],[[[231160901085152,88806658883552],[186118366523552,43764124321952]],[[445929124014304,161220639611104],[355844054891104,71135570487904]],[[194749657619552,52395415417952],[149707123057952,7352880856352]]],[[[153673563150336,59095745550336],[123637337170176,29059519570176]],[[295952053368192,106796418168192],[235879601407872,46723966207872]],[[128978484617856,34400667017856],[98942258637696,4364441037696]]],[[[38305813375872,14742425676672],[30794983546752,7231595847552]],[[73646612169984,26519836771584],[58624952511744,11498177113344]],[[32027197398912,8463809699712],[24516367569792,952979870592]]]]

private theorem identity_0108 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(827239471 / 44072960000 : ℝ)) =
      tensor4 coefficients_0108 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0108, p_headbox] <;> ring

private theorem negative_0108 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0108 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0108] at hp
  linarith only [hp]

private def coefficients_0109 : List (List (List (List ℕ))) :=
  [[[[46040597,216036394,162248597],[7110917,138177034,123318917]],[[65505437,254966074,181713437],[26575757,177106714,142783757]]],[[[88023648,423957696,320439648],[9583248,267076896,241999248]],[[127243848,502398096,359659848],[48803448,345517296,281219448]]],[[[41893272,207741744,158101272],[2382552,128720304,118590552]],[[61648632,247252464,177856632],[22137912,168231024,138345912]]]]

private theorem identity_0109 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(33091 / 6886400 : ℝ)) =
      tensor4 coefficients_0109 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0109, p_coupled] <;> ring

private theorem negative_0109 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0109 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0109] at hp
  linarith only [hp]

private theorem node_0118 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0108 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0109 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0116 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 32 : ℝ)
  · exact node_0117 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0118 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0110 : List (List (List (List ℕ))) :=
  [[[[24703931,76523062,49882331],[15116771,57348742,40295171]],[[34291091,95697382,59469491],[24703931,76523062,49882331]]],[[[47323608,148877616,97680408],[27858768,109947936,78215568]],[[66788448,187807296,117145248],[47323608,148877616,97680408]]],[[[22529898,72174996,47708298],[12652218,52419636,37830618]],[[32407578,91930356,57585978],[22529898,72174996,47708298]]]]

private theorem identity_0110 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(702901 / 6886400 : ℝ)) =
      tensor4 coefficients_0110 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0110, p_coupled] <;> ring

private theorem negative_0110 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0110 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0110] at hp
  linarith only [hp]

private theorem node_0115 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0116 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0110 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0114 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0105 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0115 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0111 : List (List (List (List ℕ))) :=
  [[[[24413411,110804422,78643811],[5239091,72455782,59469491]],[[34000571,129978742,88230971],[14826251,91630102,69056651]]],[[[47323608,218602416,155784408],[8393928,140743056,116854728]],[[66788448,257532096,175249248],[27858768,179672736,136319568]]],[[[22820418,107618436,77050818],[3065058,68107716,57295458]],[[32698098,127373796,86928498],[12942738,87863076,67173138]]]]

private theorem identity_0111 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(170281 / 6886400 : ℝ)) =
      tensor4 coefficients_0111 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0111, p_coupled] <;> ring

private theorem negative_0111 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0111 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0111] at hp
  linarith only [hp]

private theorem node_0113 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0114 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0111 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0106 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 16 : ℝ)
  · exact node_0107 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0113 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0112 : List (List (List (List ℕ))) :=
  [[[[24292123,71825846,43660123],[14995483,53232566,34363483]],[[33588763,90419126,52956763],[24292123,71825846,43660123]]],[[[46970070,140423340,85706070],[27795750,102074700,66531750]],[[66144390,178771980,104880390],[46970070,140423340,85706070]]],[[[22498389,68238378,41866389],[12620709,48483018,31988709]],[[32376069,87993738,51744069],[22498389,68238378,41866389]]]]

private theorem identity_0112 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(1402301 / 6886400 : ℝ)) =
      tensor4 coefficients_0112 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0112, p_coupled] <;> ring

private theorem negative_0112 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0112 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0112] at hp
  linarith only [hp]

private theorem node_0105 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0106 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0112 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0113 : List (List (List (List ℕ))) :=
  [[[[54500260204933,29621955744133],[47036768866693,22158464405893]],[[106868094313226,57111485391626],[91941111636746,42184502715146]],[[45370810978693,20492506517893],[37907319640453,13029015179653]]],[[[217467401356820,118287375091220],[187596776424980,88416750159380]],[[425436462812200,227076410281000],[365695212948520,167335160417320]],[[180074679068180,80894652802580],[150204054136340,51024027870740]]],[[[325352729585950,177081361957150],[280523029976350,132251662347550]],[[635009755927100,338467020669500],[545350356707900,248807621450300]],[[267955704195550,119684336566750],[223126004585950,74854636957150]]],[[[216304358668500,117788484364500],[186402863662500,87886989358500]],[[421182638367000,224150889759000],[361379648355000,164347899747000]],[[177170690050500,78654815746500],[147269195044500,48753320740500]]],[[[53918766826875,29372538346875],[46439837836875,21893609356875]],[[104741244123750,55648787163750],[89783386143750,40690929183750]],[[43918850536875,19372622056875],[36439921546875,11893693066875]]]]

private theorem identity_0113 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(2114434323 / 18052284416 : ℝ)) =
      tensor4 coefficients_0113 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0113, p_headbox] <;> ring

private theorem negative_0113 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0113 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0113] at hp
  linarith only [hp]

private def coefficients_0114 : List (List (List (List ℕ))) :=
  [[[[87412747,291033494,199747147],[50226187,216660374,162560587]],[[124599307,365406614,236933707],[87412747,291033494,199747147]]],[[[166044630,564505260,390713430],[91090470,414596940,315759270]],[[240998790,714413580,465667590],[166044630,564505260,390713430]]],[[[78452325,273112650,190786725],[40684725,197577450,153019125]],[[116219925,348647850,228554325],[78452325,273112650,190786725]]]]

private theorem identity_0114 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(180821 / 4407296 : ℝ)) =
      tensor4 coefficients_0114 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0114, p_coupled] <;> ring

private theorem negative_0114 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0114 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0114] at hp
  linarith only [hp]

private theorem node_0127 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0113 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0114 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0115 : List (List (List (List ℕ))) :=
  [[[[50776233361693,25897928900893],[43312742023453,18434437562653]],[[99420040626746,49663431705146],[84493057950266,34736449028666]],[[41646784135453,16768479674653],[34183292797213,9304988336413]]],[[[202554634404980,103374608139380],[172684009473140,73503983207540]],[[395610928908520,197250876377320],[335869679044840,137509626513640]],[[165161912116340,65981885850740],[135291287184500,36111260918900]]],[[[302959816946350,154688449317550],[258130117336750,109858749707950]],[[590223930647900,293681195390300],[500564531428700,204021796171100]],[[245562791555950,97291423927150],[200733091946350,52461724317550]]],[[[201360721642500,102844847338500],[171459226636500,72943352332500]],[[391295364315000,194263615707000],[331492374303000,134460625695000]],[[162227053024500,63711178720500],[132325558018500,33809683714500]]],[[[50179302331875,25633073851875],[42700373341875,18154144861875]],[[97262315133750,48169858173750],[82304457153750,33212000193750]],[[40179386041875,15633157561875],[32700457051875,8154228571875]]]]

private theorem identity_0115 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1449640635 / 18052284416 : ℝ)) =
      tensor4 coefficients_0115 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0115, p_headbox] <;> ring

private theorem negative_0115 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0115 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0115] at hp
  linarith only [hp]

private def coefficients_0116 : List (List (List (List ℕ))) :=
  [[[[69109987,254427974,181444387],[31923427,180054854,144257827]],[[106296547,328801094,218630947],[69109987,254427974,181444387]]],[[[128858070,490132140,353526870],[53903910,340223820,278572710]],[[203812230,640040460,428481030],[128858070,490132140,353526870]]],[[[59568525,235345050,171902925],[21800925,159809850,134135325]],[[97336125,310880250,209670525],[59568525,235345050,171902925]]]]

private theorem identity_0116 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(96893 / 4407296 : ℝ)) =
      tensor4 coefficients_0116 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0116, p_coupled] <;> ring

private theorem negative_0116 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0116 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0116] at hp
  linarith only [hp]

private theorem node_0128 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0115 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0116 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0126 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0127 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0128 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0117 : List (List (List (List ℕ))) :=
  [[[[909035508263669,510982636890869],[789619646851829,391566775479029]],[[1560047458833898,763941716088298],[1321215736010218,525109993264618]],[[539059580496629,141006709123829],[419643719084789,21590847711989]]],[[[3624873514281940,2035327561411540],[3147076792003540,1557530839133140]],[[6211403075770280,3032311170029480],[5255809631213480,2076717725472680]],[[2139469762243540,549923809373140],[1661673039965140,72127087094740]]],[[[5420233624716478,3039908531954878],[4703343534978238,2323018442216638]],[[9273593266638716,4512943081115516],[7839813087162236,3079162901639036]],[[3183893209583038,803568116821438],[2467003119844798,86678027083198]]],[[[3601988889540148,2017765077136948],[3123935420792788,1539711608389588]],[[6153167465502536,2984719840696136],[5197060528007816,2028612903201416]],[[2105615628723988,521391816320788],[1627562159976628,43338347573428]]],[[[897593267434379,502201466295179],[778049027558699,382657226419499]],[[1530929808985078,740146206706678],[1291841329233718,501057726955318]],[[522132597480299,126740796341099],[402588357604619,7196556465419]]]]

private theorem identity_0117 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(7196556465419 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0117 ((x0-0)/(1 / 64 : ℝ)) (1-((x0-0)/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0117, p_headbox] <;> ring

private theorem negative_0117 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0117 ((x0-0)/(1 / 64 : ℝ)) (1-((x0-0)/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0117] at hp
  linarith only [hp]

private def coefficients_0118 : List (List (List (List ℕ))) :=
  [[[[397956080274899,200260179705299],[338183960337059,140488059767459]],[[729847979078878,334456177939678],[610303739203198,214911938063998]],[[317991405795179,120295505225579],[258219285857339,60523385287739]]],[[[1586016411198280,796561112843080],[1346866186069240,557410887714040]],[[2906221949023640,1327311352313240],[2427921498765560,849010902055160]],[[1264696962159760,475241663804560],[1025546737030720,236091438675520]]],[[[2370226032296600,1188033309455000],[2011410515161400,829217792319800]],[[4339408683959200,1975023238276000],[3621777649688800,1257392204005600]],[[1886059725837800,703867002996200],[1527244208702600,345051485861000]]],[[[1574227220232000,787424067336000],[1334958376368000,548155223472000]],[[2879543579532000,1305937273740000],[2401005891804000,827399586012000]],[[1249994262612000,463191109716000],[1010725418748000,223922265852000]]],[[[392061517155000,195691689315000],[332230085235000,135860257395000]],[[716508862110000,323769206430000],[596845998270000,204106342590000]],[[310640091435000,114270263595000],[250808659515000,54438831675000]]]]

private theorem identity_0118 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1209751815 / 18052284416 : ℝ)) =
      tensor4 coefficients_0118 ((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0118, p_headbox] <;> ring

private theorem negative_0118 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0118 ((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0118] at hp
  linarith only [hp]

private def coefficients_0119 : List (List (List (List ℕ))) :=
  [[[[101653091,451216582,341816291],[26698931,301308262,266862131]],[[139130171,526170742,379293371],[64176011,376262422,304339211]]],[[[195217320,886255440,675543720],[44727960,585276720,525054360]],[[270462000,1036744800,750788400],[119972640,735766080,600299040]]],[[[93474450,434859300,333637650],[17939250,283788900,258102450]],[[131242050,510394500,371405250],[55706850,359324100,295870050]]]]

private theorem identity_0119 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(39865 / 4407296 : ℝ)) =
      tensor4 coefficients_0119 ((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0119, p_coupled] <;> ring

private theorem negative_0119 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0119 ((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0119] at hp
  linarith only [hp]

private theorem node_0132 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0118 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0119 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0131 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 64 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0117 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0132 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0120 : List (List (List (List ℕ))) :=
  [[[[105715507,327639014,218049907],[68528947,253265894,180863347]],[[142902067,402012134,255236467],[105715507,327639014,218049907]]],[[[203231190,638878380,427899990],[128277030,488970060,352945830]],[[278185350,788786700,502854150],[203231190,638878380,427899990]]],[[[97336125,310880250,209670525],[59568525,235345050,171902925]],[[135103725,386415450,247438125],[97336125,310880250,209670525]]]]

private theorem identity_0120 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(264749 / 4407296 : ℝ)) =
      tensor4 coefficients_0120 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0120, p_coupled] <;> ring

private theorem negative_0120 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0120 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0120] at hp
  linarith only [hp]

private theorem node_0130 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0131 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0120 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0121 : List (List (List (List ℕ))) :=
  [[[[111626848,161208928],[681113216,780277376],[576458848,626040928]],[[671816576,770980736],[2275621312,2473949632],[1617749696,1716913856]],[[567162208,616744288],[1608453056,1707617216],[1048263328,1097845408]]],[[[326355664,425519824],[1572207128,1770535448],[1259796424,1358960584]],[[1553613848,1751942168],[4978757536,5375414176],[3453033608,3651361928]],[[1241203144,1340367304],[3434440328,3632768648],[2207182144,2306346304]]],[[[215074817,264656897],[891785914,990950074],[683683577,733265657]],[[882489274,981653434],[2704520228,2902848548],[1835975914,1935140074]],[[674386937,723969017],[1826679274,1925843434],[1159264817,1208846897]]]]

private theorem identity_0121 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(3488339 / 21692160 : ℝ)) =
      tensor4 coefficients_0121 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0121, p_variance] <;> ring

private theorem negative_0121 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0121 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0121] at hp
  linarith only [hp]

private theorem node_0129 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0130 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0121 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0125 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0126 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0129 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0122 : List (List (List (List ℕ))) :=
  [[[[27264799076963,14991684836963],[23525334581963,11252220341963]],[[52981453388926,28435224908926],[45502524398926,20956295918926]],[[22264840931963,9991726691963],[18525376436963,6252262196963]]],[[[108744550627352,59817573859352],[93779582170352,44852605402352]],[[210816982619704,112963029083704],[180887045705704,83033092169704]],[[88311719776352,39384743008352],[73346751319352,24419774551352]]],[[[162620984691128,89478182028728],[140163472024328,67020669361928]],[[314516880309856,168231274985056],[269601854976256,123316249651456]],[[131324482369928,58181679707528],[108866969703128,35724167040728]]],[[[108067538366592,59470406385792],[93089557809312,44492425828512]],[[208508681534304,111314417572704],[178552720419744,81358456458144]],[[86773199798112,38176067817312],[71795219240832,23198087260032]]],[[[26926303522072,14818111675672],[23180331669592,11072139823192]],[[51827327047664,27610943354864],[44335383342704,20118999649904]],[[21495594568792,9387402722392],[17749622716312,5641430869912]]]]

private theorem identity_0122 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(705178858739 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0122 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0122, p_headbox] <;> ring

private theorem negative_0122 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0122 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0122] at hp
  linarith only [hp]

private def coefficients_0123 : List (List (List (List ℕ))) :=
  [[[[41701307,141506614,97868507],[22817507,103739014,78984707]],[[60585107,179274214,116752307],[41701307,141506614,97868507]]],[[[78832624,273873248,191167024],[40774504,197757008,153108904]],[[116890744,349989488,229225144],[78832624,273873248,191167024]]],[[[37041538,132187076,93208738],[17867218,93838436,74034418]],[[56215858,170535716,112383058],[37041538,132187076,93208738]]]]

private theorem identity_0123 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(8933609 / 247910400 : ℝ)) =
      tensor4 coefficients_0123 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0123, p_coupled] <;> ring

private theorem negative_0123 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0123 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0123] at hp
  linarith only [hp]

private theorem node_0135 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0122 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0123 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0124 : List (List (List (List ℕ))) :=
  [[[[25398320508203,13125206268203],[21658856013203,9385741773203]],[[49248496251406,24702267771406],[41769567261406,17223338781406]],[[20398362363203,8125248123203],[16658897868203,4385783628203]]],[[[101271525875312,52344549107312],[86306557418312,37379580650312]],[[195870933115624,98016979579624],[165940996201624,68087042665624]],[[80838695024312,31911718256312],[65873726567312,16946749799312]]],[[[151401387581768,78258584919368],[128943874914968,55801072252568]],[[292077686091136,145792080766336],[247162660757536,100877055432736]],[[120104885260568,46962082598168],[97647372593768,24504569931368]]],[[[100581501514272,51984369533472],[85603520956992,37006388976192]],[[193536607829664,96342343868064],[163580646715104,66386382753504]],[[79287162945792,30690030964992],[64309182388512,15712050407712]]],[[[25053317595832,12945125749432],[21307345743352,9199153896952]],[[48081355195184,23864971502384],[40589411490224,16373027797424]],[[19622608642552,7514416796152],[15876636790072,3768444943672]]]]

private theorem identity_0124 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(471055617959 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0124 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0124, p_headbox] <;> ring

private theorem negative_0124 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0124 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0124] at hp
  linarith only [hp]

private def coefficients_0125 : List (List (List (List ℕ))) :=
  [[[[32404667,122913334,88571867],[13520867,85145734,69688067]],[[51288467,160680934,107455667],[32404667,122913334,88571867]]],[[[59948824,236105648,172283224],[21890704,159989408,134225104]],[[98006944,312221888,210341344],[59948824,236105648,172283224]]],[[[27454378,113012756,83621578],[8280058,74664116,64447258]],[[46628698,151361396,102795898],[27454378,113012756,83621578]]]]

private theorem identity_0125 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(4140029 / 247910400 : ℝ)) =
      tensor4 coefficients_0125 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0125, p_coupled] <;> ring

private theorem negative_0125 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0125 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0125] at hp
  linarith only [hp]

private theorem node_0136 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0124 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0125 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0134 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0135 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0136 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0126 : List (List (List (List ℕ))) :=
  [[[[790372234620301,397632578940301],[670709370780301,277969715100301]],[[1445516124840602,660036813480602],[1206190397160602,420711085800602]],[[627529383180301,234789727500301],[507866519340301,115126863660301]]],[[[3149526635257204,1581215695609204],[2670761412265204,1102450472617204]],[[5755048237178408,2618426357882408],[4797517791194408,1660895911898408]],[[2495249738977204,926938799329204],[2016484515985204,448173576337204]]],[[[4706173447111006,2357674099859806],[3987859807048606,1639360459797406]],[[8591710198538012,3894711504035612],[7155082918413212,2458084223910812]],[[3720407891073406,1371908543822206],[3002094251011006,653594903759806]]],[[[3125256049569444,1562231551291044],[2646272972601924,1083248474323524]],[[5700340442380728,2574291445823928],[4742374288445688,1616325291888888]],[[2465184232776084,902159734497684],[1986201155808564,423176657530164]]],[[[778236999687779,388140564692579],[658465203630659,268368768635459]],[[1418162349365398,637969479374998],[1178618757251158,398425887260758]],[[612496694092019,222400259096819],[492724898034899,102628463039699]]]]

private theorem identity_0126 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(102628463039699 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0126 ((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0126, p_headbox] <;> ring

private theorem negative_0126 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0126 ((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0126] at hp
  linarith only [hp]

private def coefficients_0127 : List (List (List (List ℕ))) :=
  [[[[195888139,887597078,676214539],[44817739,585456278,525144139]],[[271423339,1038667478,751749739],[120352939,736526678,600679339]]],[[[375239438,1742120476,1335892238],[71936558,1135514716,1032589358]],[[526890878,2045423356,1487543678],[223587998,1438817596,1184240798]]],[[[179171741,854164282,659498141],[26939261,549699322,507265661]],[[255287981,1006396762,735614381],[103055501,701931802,583381901]]]]

private theorem identity_0127 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(26939261 / 3966566400 : ℝ)) =
      tensor4 coefficients_0127 ((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0127, p_coupled] <;> ring

private theorem negative_0127 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0127 ((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0127] at hp
  linarith only [hp]

private theorem node_0140 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0126 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0127 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0128 : List (List (List (List ℕ))) :=
  [[[[392325246999067,197277029501467],[332439348970507,137391131472907]],[[715494668993054,325398233997854],[595722872935934,205626437940734]],[[309455094201187,114406876703587],[249569196172627,54520978675027]]],[[[1563146962587104,784273471745504],[1323551316842384,544677826000784]],[[2848133153512648,1290386171829448],[2368941862023208,811194880340008]],[[1230221648600744,451348157759144],[990626002856024,211752512014424]]],[[[2335403054031584,1169069655298784],[1975933912217504,809600513484704]],[[4251262930373728,1918596132908128],[3532324646745568,1199657849279968]],[[1833852059243744,667518660510944],[1474382917429664,308049518696864]]],[[[1550666262801920,774427067870720],[1310971319064320,534732124133120]],[[2820105191290240,1267626801427840],[2340715303815040,788236913952640]],[[1214859610094720,438620415163520],[975164666357120,198925471425920]]],[[[386084922654592,192353853112192],[326149373014912,132418303472512]],[[701480742028544,314018602943744],[581609642749184,194147503664384]],[[301774103546752,108043034004352],[241838553907072,48107484364672]]]]

private theorem identity_0128 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(375839721599 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0128 ((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0128, p_headbox] <;> ring

private theorem negative_0128 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0128 ((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0128] at hp
  linarith only [hp]

private def coefficients_0129 : List (List (List (List ℕ))) :=
  [[[[94145269,436200938,334308469],[18029029,283968458,258192229]],[[132203389,512317178,372366589],[56087149,360084698,296250349]]],[[[179842560,855505920,660168960],[27029040,549878880,507355440]],[[256249320,1008319440,736575720],[103435800,702692400,583762200]]],[[[85607512,419125424,325770712],[8910232,265730864,249073432]],[[123956152,495822704,364119352],[47258872,342428144,287422072]]]]

private theorem identity_0129 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(1113779 / 247910400 : ℝ)) =
      tensor4 coefficients_0129 ((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0129, p_coupled] <;> ring

private theorem negative_0129 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0129 ((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0129] at hp
  linarith only [hp]

private theorem node_0141 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0128 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0129 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0139 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 64 : ℝ)
  · exact node_0140 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0141 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0130 : List (List (List (List ℕ))) :=
  [[[[50997947,160099894,107165147],[32114147,122332294,88281347]],[[69881747,197867494,126048947],[50997947,160099894,107165147]]],[[[97716424,311640848,210050824],[59658304,235524608,171992704]],[[135774544,387757088,248108944],[97716424,311640848,210050824]]],[[[46628698,151361396,102795898],[27454378,113012756,83621578]],[[65803018,189710036,121970218],[46628698,151361396,102795898]]]]

private theorem identity_0130 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(13727189 / 247910400 : ℝ)) =
      tensor4 coefficients_0130 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0130, p_coupled] <;> ring

private theorem negative_0130 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0130 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0130] at hp
  linarith only [hp]

private theorem node_0138 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0139 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0130 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0131 : List (List (List (List ℕ))) :=
  [[[[326701665,425865825],[1576675890,1775004210],[1263919185,1363083345]],[[1558082610,1756410930],[4995248580,5391905220],[3465055890,3663384210]],[[1245325905,1344490065],[3446462610,3644790930],[2215081665,2314245825]]],[[[860991270,1059319590],[3576081180,3972737820],[2742979830,2941308150]],[[3538894620,3935551260],[10851063000,11644376280],[7367948220,7764604860]],[[2705793270,2904121590],[7330761660,7727418300],[4652858310,4851186630]]],[[[534981607,634145767],[2000789294,2199117614],[1479752647,1578916807]],[[1982196014,2180524334],[5858582428,6255239068],[3904276334,4102604654]],[[1461159367,1560323527],[3885683054,4084011374],[2438468647,2537632807]]]]

private theorem identity_0131 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(7260037 / 30851072 : ℝ)) =
      tensor4 coefficients_0131 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0131, p_variance] <;> ring

private theorem negative_0131 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0131 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0131] at hp
  linarith only [hp]

private theorem node_0137 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0138 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0131 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0133 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0134 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0137 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0124 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 32 : ℝ)
  · exact node_0125 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0133 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0132 : List (List (List (List ℕ))) :=
  [[[[41926139,138082678,92282939],[23332859,100896118,73689659]],[[60519419,175269238,110876219],[41926139,138082678,92282939]]],[[[79461846,267384492,180175446],[41694246,191849292,142407846]],[[117229446,342919692,217943046],[79461846,267384492,180175446]]],[[[37356149,128942698,87712949],[18181829,90594058,68538629]],[[56530469,167291338,106887269],[37356149,128942698,87712949]]]]

private theorem identity_0132 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(18181829 / 247910400 : ℝ)) =
      tensor4 coefficients_0132 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0132, p_coupled] <;> ring

private theorem negative_0132 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0132 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0132] at hp
  linarith only [hp]

private theorem node_0123 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0124 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0132 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0133 : List (List (List (List ℕ))) :=
  [[[[28778272,53569312],[285324224,334906304],[263518432,288309472]],[[283000064,332582144],[1037804608,1136968768],[768749504,818331584]],[[261194272,285985312],[766425344,816007424],[512203552,536994592]]],[[[109107528,158689608],[677527176,776691336],[582364608,631946688]],[[672878856,772043016],[2296920192,2495248512],[1651931256,1751095416]],[[577716288,627298368],[1647282936,1746447096],[1083511608,1133093688]]],[[[80675257,105466297],[392894954,442477034],[319192177,343983217]],[[390570794,440152874],[1260499588,1359663748],[883873754,933455834]],[[316868017,341659057],[881549594,931131674],[571654057,596445097]]]]

private theorem identity_0133 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(899321 / 5423040 : ℝ)) =
      tensor4 coefficients_0133 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0133, p_variance] <;> ring

private theorem negative_0133 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0133 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0133] at hp
  linarith only [hp]

private theorem node_0122 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0123 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0133 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0134 : List (List (List (List ℕ))) :=
  [[[[26454112,51245152],[513091904,562673984],[514527712,539318752]],[[276027584,325609664],[1504960768,1604124928],[1284713024,1334295104]],[[256545952,281336992],[1005813824,1055395904],[777157792,801948832]]],[[[104459208,154041288],[1136839296,1236003456],[1088159928,1137742008]],[[658933896,758098056],[3238786032,3437114352],[2691411816,2790575976]],[[568419648,618001728],[2129836656,2229000816],[1617196848,1666778928]]],[[[78351097,103142137],[624439394,674021474],[573978217,598769257]],[[383598314,433180394],[1735209268,1834373428],[1407390794,1456972874]],[[312219697,337010737],[1124714834,1174296914],[840385057,865176097]]]]

private theorem identity_0134 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(826691 / 5423040 : ℝ)) =
      tensor4 coefficients_0134 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0134, p_variance] <;> ring

private theorem negative_0134 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0134 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0134] at hp
  linarith only [hp]

private theorem node_0121 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0122 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0134 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0135 : List (List (List (List ℕ))) :=
  [[[[54506460818549,30290077125749],[47014517113589,22798133420789]],[[104962361644138,56529594258538],[89978474234218,41545706848618]],[[43645042911989,19428659219189],[36153099207029,11936715514229]]],[[[217301194717588,120764389136788],[187321606192468,90784800611668]],[[417450699889256,224377088727656],[357491522839016,164417911677416]],[[172998528602068,76461723021268],[143018940076948,46482134496148]]],[[[324817200689038,180503970506638],[279831293123758,135518062941358]],[[622487525788796,333861065423996],[532515710658236,243889250293436]],[[257082229110958,112768998928558],[212096321545678,67783091363278]]],[[[215756695986340,119875117592740],[185755866381940,89874287988340]],[[412472481661880,220709324874680],[352470822453080,160707665665880]],[[169749091752340,73867513358740],[139748262147940,43866683754340]]],[[[53734225788779,29845455689579],[46231658929499,22342888830299]],[[102473287303078,54695747104678],[87468153584518,39690613386118]],[[42020344923899,18131574824699],[34517778064619,10629007965419]]]]

private theorem identity_0135 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(10629007965419 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0135 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0135, p_headbox] <;> ring

private theorem negative_0135 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0135 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0135] at hp
  linarith only [hp]

private def coefficients_0136 : List (List (List (List ℕ))) :=
  [[[[79212923,274633846,191547323],[40864283,197936566,153198683]],[[117561563,351331126,229895963],[79212923,274633846,191547323]]],[[[148926750,530269500,373595550],[71648430,375712860,296317230]],[[226205070,684826140,450873870],[148926750,530269500,373595550]]],[[[69534269,255276538,181868669],[30604589,177417178,142938989]],[[108463949,333135898,220798349],[69534269,255276538,181868669]]]]

private theorem identity_0136 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(30604589 / 991641600 : ℝ)) =
      tensor4 coefficients_0136 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0136, p_coupled] <;> ring

private theorem negative_0136 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0136 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0136] at hp
  linarith only [hp]

private theorem node_0148 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0135 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0136 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0137 : List (List (List (List ℕ))) :=
  [[[[50765800543229,26549416850429],[43273856838269,19057473145469]],[[97481041093498,49048273707898],[82497153683578,34064386297978]],[[39904382636669,15687998943869],[32412438931709,8196055238909]]],[[[202326739911028,105789934330228],[172347151385908,75810345805108]],[[387501790276136,194428179114536],[327542613225896,134469002064296]],[[158024073795508,61487268214708],[128044485270388,31507679689588]]],[[[302338993701598,158025763519198],[257353086136318,113039855953918]],[[577531111813916,288904651449116],[487559296683356,198932836318556]],[[234604022123518,90290791941118],[189618114558238,45304884375838]]],[[[200761000100500,104879421706900],[170760170496100,74878592102500]],[[382481089890200,190717933103000],[322479430681400,130716273894200]],[[154753395866500,58871817472900],[124752566262100,28870987868500]]],[[[49982942359139,26094172259939],[42480375499859,18591605400659]],[[94970720443798,47193180245398],[79965586725238,32188046526838]],[[38269061494259,14380291395059],[30766494634979,6877724535779]]]]

private theorem identity_0137 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6877724535779 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0137 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0137, p_headbox] <;> ring

private theorem negative_0137 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0137 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0137] at hp
  linarith only [hp]

private def coefficients_0138 : List (List (List (List ℕ))) :=
  [[[[60329123,236866246,172663523],[21980483,160168966,134314883]],[[98677763,313563526,211012163],[60329123,236866246,172663523]]],[[[110578110,453572220,335246910],[33299790,299015580,257968590]],[[187856430,608128860,412525230],[110578110,453572220,335246910]]],[[[50069429,216346858,162403829],[11139749,138487498,123474149]],[[88999109,294206218,201333509],[50069429,216346858,162403829]]]]

private theorem identity_0138 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(11139749 / 991641600 : ℝ)) =
      tensor4 coefficients_0138 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0138, p_coupled] <;> ring

private theorem negative_0138 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0138 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0138] at hp
  linarith only [hp]

private theorem node_0149 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0137 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0138 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0147 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0148 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0149 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0139 : List (List (List (List ℕ))) :=
  [[[[778747321812829,391285182728029],[658876222533469,271414083448669]],[[1416116437064378,641192158894778],[1176374238505658,401449960336058]],[[610125683597149,222663544512349],[490254584317789,102792445232989]]],[[[3102336142884212,1555117420068212],[2622757236124532,1075538513308532]],[[5636101301905384,2541663856273384],[4676943488386024,1582506042754024]],[[2424976342573172,877757619757172],[1945397435813492,398178712997492]]],[[[4634352100882414,2317464304556014],[3914846759400814,1597958963074414]],[[8411268900678428,3777493308025628],[6972258217715228,2338482625062428]],[[3614010626616814,1297122830290414],[2894505285135214,577617488808814]]],[[[3076685155740852,1534717175196852],[2596926785480532,1054958804936532]],[[5578699846854744,2494763885766744],[4619183106334104,1535247145246104]],[[2393595067481892,851627086937892],[1913836697221572,371868716677572]]],[[[765921872522259,381085104573459],[645961036263219,261124268314419]],[[1387415804202198,617742268304598],[1147494131684118,377820595786518]],[[594435096433539,209598328484739],[474474260174499,89637492225699]]]]

private theorem identity_0139 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(9959721358411 / 180522844160000 : ℝ)) =
      tensor4 coefficients_0139 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0139, p_headbox] <;> ring

private theorem negative_0139 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0139 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0139] at hp
  linarith only [hp]

private def coefficients_0140 : List (List (List (List ℕ))) :=
  [[[[180513379,856847558,660839779],[27118819,550058438,507445219]],[[257210659,1010242118,737537059],[103816099,703452998,584142499]]],[[[343771686,1679184972,1304424486],[35820486,1063282572,996473286]],[[497747286,1987136172,1458400086],[189796086,1371233772,1150448886]]],[[[163078749,821978298,643405149],[8522109,512865018,488848509]],[[240357069,976534938,720683469],[85800429,667421658,566126829]]]]

private theorem identity_0140 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(946901 / 440729600 : ℝ)) =
      tensor4 coefficients_0140 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0140, p_coupled] <;> ring

private theorem negative_0140 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0140 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0140] at hp
  linarith only [hp]

private theorem node_0153 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0139 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0140 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0141 : List (List (List (List ℕ))) :=
  [[[[91368729,289697049],[3809589138,4206245778],[3774000249,3972328569]],[[3716622738,4113279378],[14817101796,15610415076],[11212038738,11608695378]],[[3681033849,3879362169],[11119072338,11515728978],[7493818329,7692146649]]],[[[586958310,983614950],[8442727020,9236040300],[7967328390,8363985030]],[[8256794220,9050107500],[31311515160,32898141720],[23277840300,24071153580]],[[7781395590,8178052230],[23091907500,23885220780],[15422071590,15818728230]]],[[[496281583,694609903],[4634521886,5031178526],[4194020143,4392348463]],[[4541555486,4938212126],[16497181372,17290494652],[12067185566,12463842206]],[[4101053743,4299382063],[11974219166,12370875806],[7928945263,8127273583]]]]

private theorem identity_0141 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(10152081 / 617021440 : ℝ)) =
      tensor4 coefficients_0141 ((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0141, p_variance] <;> ring

private theorem negative_0141 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0141 ((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0141] at hp
  linarith only [hp]

private theorem node_0152 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 64 : ℝ)
  · exact node_0153 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0141 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0142 : List (List (List (List ℕ))) :=
  [[[[98096723,312401446,210431123],[59748083,235704166,172082483]],[[136445363,389098726,248779763],[98096723,312401446,210431123]]],[[[187275390,606966780,411944190],[109997070,452410140,334665870]],[[264553710,761523420,489222510],[187275390,606966780,411944190]]],[[[88999109,294206218,201333509],[50069429,216346858,162403829]],[[127928789,372065578,240263189],[88999109,294206218,201333509]]]]

private theorem identity_0142 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(50069429 / 991641600 : ℝ)) =
      tensor4 coefficients_0142 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0142, p_coupled] <;> ring

private theorem negative_0142 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0142 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0142] at hp
  linarith only [hp]

private theorem node_0151 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0152 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0142 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0143 : List (List (List (List ℕ))) :=
  [[[[215420818,265002898],[896254676,995418836],[687806338,737388418]],[[886958036,986122196],[2721011272,2919339592],[1847998196,1947162356]],[[678509698,728091778],[1838701556,1937865716],[1167164338,1216746418]]],[[[535327608,634491768],[2005258056,2203586376],[1483875408,1583039568]],[[1986664776,2184993096],[5875073472,6271730112],[3916298616,4114626936]],[[1465282128,1564446288],[3897705336,4096033656],[2446368168,2545532328]]],[[[320252791,369834871],[1109695382,1208859542],[796415071,845997151]],[[1100398742,1199562902],[3155446204,3353774524],[2068992422,2168156582]],[[787118431,836700511],[2059695782,2158859942],[1279549831,1329131911]]]]

private theorem identity_0143 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(107710409 / 347074560 : ℝ)) =
      tensor4 coefficients_0143 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0143, p_variance] <;> ring

private theorem negative_0143 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0143 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0143] at hp
  linarith only [hp]

private theorem node_0150 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0151 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0143 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0146 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0147 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0150 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0144 : List (List (List (List ℕ))) :=
  [[[[27215497538987,15271112489387],[23464214109347,11519829059747]],[[51933412940734,28044642841534],[44430846081454,20542075982254]],[[21358557106547,9414172056947],[17607273676907,5662888627307]]],[[[108452093740336,60837802540336],[93442241105416,45827949905416]],[[206443985538152,111215403138152],[176424280268312,81195697868312]],[[84600372397816,36986081197816],[69590519762896,21976228562896]]],[[[162039529718432,90862408617632],[139518262437632,68341141336832]],[[307686381280864,165332139079264],[262643846719264,120289604517664]],[[125628286252832,54451165152032],[103107018972032,31929897871232]]],[[[107584779300096,60295870500096],[92566666310016,45277757510016]],[[203774485667712,109196668067712],[173738259687552,79160442087552]],[[82889700767616,35600791967616],[67871587777536,20582678977536]]],[[[26781844079232,15000150229632],[23026429164672,11244735315072]],[[50598673576704,27035285877504],[43087843747584,19524456048384]],[[20503228102272,8721534252672],[16747813187712,4966119338112]]]]

private theorem identity_0144 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4310867481 / 44072960000 : ℝ)) =
      tensor4 coefficients_0144 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0144, p_headbox] <;> ring

private theorem negative_0144 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0144 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0144] at hp
  linarith only [hp]

private def coefficients_0145 : List (List (List (List ℕ))) :=
  [[[[37421837,132947674,93589037],[17956997,94017994,74124197]],[[56886677,171877354,113053877],[37421837,132947674,93589037]]],[[[69914568,256037136,182248968],[30694368,177596736,143028768]],[[109134768,334477536,221469168],[69914568,256037136,182248968]]],[[[32402952,122909904,88570152],[12647592,83399184,68814792]],[[52158312,162420624,108325512],[32402952,122909904,88570152]]]]

private theorem identity_0145 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(175661 / 6886400 : ℝ)) =
      tensor4 coefficients_0145 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0145, p_coupled] <;> ring

private theorem negative_0145 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0145 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0145] at hp
  linarith only [hp]

private theorem node_0156 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0144 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0145 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0146 : List (List (List (List ℕ))) :=
  [[[[82752929,181917089],[1071347218,1269675538],[1002539249,1101703409]],[[1057402258,1255730578],[3959025476,4355682116],[2929513138,3127841458]],[[988594289,1087758449],[2915568178,3113896498],[1940918849,2040083009]]],[[[368308286,566636606],[2555852812,2952509452],[2215434446,2413762766]],[[2527962892,2924619532],[8759474744,9552788024],[6287291692,6683948332]],[[2187544526,2385872846],[6259401772,6656058412],[4099747166,4298075486]]],[[[286247359,385411519],[1485889598,1684217918],[1213587199,1312751359]],[[1471944638,1670272958],[4803217276,5199873916],[3359162558,3557490878]],[[1199642239,1298806399],[3345217598,3543545918],[2159520319,2258684479]]]]

private theorem identity_0146 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(11821847 / 198328320 : ℝ)) =
      tensor4 coefficients_0146 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0146, p_variance] <;> ring

private theorem negative_0146 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0146 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0146] at hp
  linarith only [hp]

private theorem node_0155 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0156 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0146 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0147 : List (List (List (List ℕ))) :=
  [[[[73456289,172620449],[1967891938,2166220258],[1950215489,2049379649]],[[1034160658,1232488978],[5775356516,6172013156],[4852755538,5051083858]],[[974649329,1073813489],[3835354498,4033682818],[2916485009,3015649169]]],[[[349715006,548043326],[4356495772,4753152412],[4118340446,4316668766]],[[2481479692,2878136332],[12407243864,13200557144],[10148883532,10545540172]],[[2159654606,2357982926],[8106527932,8503184572],[6058433006,6256761326]]],[[[276950719,376114879],[2389987838,2588316158],[2168816959,2267981119]],[[1448703038,1647031358],[6634655356,7031311996],[5297511998,5495840318]],[[1185697279,1284861439],[4272557438,4470885758],[3142639999,3241804159]]]]

private theorem identity_0147 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(73456289 / 1388298240 : ℝ)) =
      tensor4 coefficients_0147 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0147, p_variance] <;> ring

private theorem negative_0147 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0147 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0147] at hp
  linarith only [hp]

private theorem node_0154 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0155 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0147 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0145 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 32 : ℝ)
  · exact node_0146 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0154 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0148 : List (List (List (List ℕ))) :=
  [[[[20055611,67226422,45234011],[10468451,48052102,35646851]],[[29642771,86400742,54821171],[20055611,67226422,45234011]]],[[[37736448,129703296,88093248],[18271608,90773616,68628408]],[[57201288,168632976,107558088],[37736448,129703296,88093248]]],[[[17591058,62297316,42769458],[7713378,42541956,32891778]],[[27468738,82052676,52647138],[17591058,62297316,42769458]]]]

private theorem identity_0148 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(428521 / 6886400 : ℝ)) =
      tensor4 coefficients_0148 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0148, p_coupled] <;> ring

private theorem negative_0148 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0148 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0148] at hp
  linarith only [hp]

private theorem node_0144 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0145 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0148 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0149 : List (List (List (List ℕ))) :=
  [[[[109453529,159035609],[681995938,781160098],[586487369,636069449]],[[677347618,776511778],[2313411236,2511739556],[1663953538,1763117698]],[[581839049,631421129],[1659305218,1758469378],[1091411129,1140993209]]],[[[323393030,422557190],[1580517340,1778845660],[1285014230,1384178390]],[[1571220700,1769549020],[5074980440,5471637080],[3559539580,3757867900]],[[1275717590,1374881750],[3550242940,3748571260],[2302415270,2401579430]]],[[[214631503,264213583],[899905406,999069566],[699218863,748800943]],[[895257086,994421246],[2764337212,2962665532],[1896970046,1996134206]],[[694570543,744152623],[1892321726,1991485886],[1211696143,1261278223]]]]

private theorem identity_0149 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(109453529 / 347074560 : ℝ)) =
      tensor4 coefficients_0149 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0149, p_variance] <;> ring

private theorem negative_0149 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0149 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0149] at hp
  linarith only [hp]

private theorem node_0143 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0144 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0149 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0150 : List (List (List (List ℕ))) :=
  [[[[104805209,154387289],[1145084818,1244248978],[1096059449,1145641529]],[[663402658,762566818],[3262830596,3461158916],[2710987618,2810151778]],[[572542409,622124489],[2145635698,2244799858],[1628873129,1678455209]]],[[[314096390,413260550],[2514248620,2712576940],[2311711910,2410876070]],[[1543330780,1741659100],[6988926200,7385582840],[5668714780,5867043100]],[[1257124310,1356288470],[4530457420,4728785740],[3384892790,3484056950]]],[[[209983183,259565263],[1370547806,1469711966],[1216344463,1265926543]],[[881312126,980476286],[3728863612,3927191932],[2959111166,3058275326]],[[685273903,734855983],[2386205726,2485369886],[1756711663,1806293743]]]]

private theorem identity_0150 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(104805209 / 347074560 : ℝ)) =
      tensor4 coefficients_0150 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0150, p_variance] <;> ring

private theorem negative_0150 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0150 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0150] at hp
  linarith only [hp]

private theorem node_0142 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0143 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0150 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0120 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 16 : ℝ)
  · exact node_0121 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0142 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0151 : List (List (List (List ℕ))) :=
  [[[[19934323,63110246,39302323],[10637683,44516966,30005683]],[[29230963,81703526,48598963],[19934323,63110246,39302323]]],[[[37673430,121830060,76409430],[18499110,83481420,57235110]],[[56847750,160178700,95583750],[37673430,121830060,76409430]]],[[[17559549,58360698,36927549],[7681869,38605338,27049869]],[[27437229,78116058,46805229],[17559549,58360698,36927549]]]]

private theorem identity_0151 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(853541 / 6886400 : ℝ)) =
      tensor4 coefficients_0151 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0151, p_coupled] <;> ring

private theorem negative_0151 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0151 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0151] at hp
  linarith only [hp]

private theorem node_0119 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0120 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0151 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0104 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0105 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0119 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0152 : List (List (List (List ℕ))) :=
  [[[[15092323,92162246,61575523],[5795683,73568966,52278883]],[[24388963,110755526,70872163],[15092323,92162246,61575523]]],[[[29151510,182258220,122117910],[9977190,143909580,102943590]],[[48325830,220606860,141292230],[29151510,182258220,122117910]]],[[[13879629,89736858,60362829],[4001949,69981498,50485149]],[[23757309,109492218,70240509],[13879629,89736858,60362829]]]]

private theorem identity_0152 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(444661 / 6886400 : ℝ)) =
      tensor4 coefficients_0152 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0152, p_coupled] <;> ring

private theorem negative_0152 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0152 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0152] at hp
  linarith only [hp]

private def coefficients_0153 : List (List (List (List ℕ))) :=
  [[[[35375008,47770528],[193930496,218721536],[165527968,177923488]],[[189282176,214073216],[641194432,690776512],[465857216,490648256]],[[160879648,173275168],[461208896,485999936],[307301728,319697248]]],[[[98413888,123204928],[446965496,496547576],[362496568,387287608]],[[437668856,487250936],[1408151392,1507315552],[998372456,1047954536]],[[353199928,377990968],[989075816,1038657896],[649820848,674611888]]],[[[63384881,75780401],[253727002,278518042],[197314601,209710121]],[[249078682,273869722],[768340964,817923044],[533207242,557998282]],[[192666281,205061801],[528558922,553349962],[342865121,355260641]]]]

private theorem identity_0153 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(1105469 / 1355760 : ℝ)) =
      tensor4 coefficients_0153 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0153, p_variance] <;> ring

private theorem negative_0153 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0153 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0153] at hp
  linarith only [hp]

private theorem node_0157 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0152 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0153 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 4 : ℝ)
  · exact node_0104 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0157 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part04
