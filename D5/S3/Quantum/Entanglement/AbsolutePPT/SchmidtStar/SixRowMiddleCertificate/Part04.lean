/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part04Node0121
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part04Node0142
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

private theorem node_0120 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 16 : ℝ)
  · exact SixRowMiddleCertificate.Subtrees.Part04Node0121.exclude x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact SixRowMiddleCertificate.Subtrees.Part04Node0142.exclude x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

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
