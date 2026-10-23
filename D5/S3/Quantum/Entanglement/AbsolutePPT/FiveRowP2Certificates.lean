/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP2Certificates
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: All upper and small-q n19 rational Bernstein certificate coefficients. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Scalar
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
open FiveRowP2Scalar
noncomputable section
/- Complete frozen degree-2 and degree-4 tables. Multinomial factors have
been multiplied into their rational coefficients. Python only transcribes;
identity proofs below use ring and signs use ordered real arithmetic. -/

private def upperP1 (H D s : ℝ) : ℝ :=
  (19713572/10476675)*(s/3)*(1-H/3-D/3-s/3) +
    (134561/136950)*(s/3)^2 +
    (849877241/932424075)*(D/3)*(1-H/3-D/3-s/3) +
    (87719/45650)*(D/3)*(s/3) +
    (9976/22825)*(D/3)^2 +
    (15112699/17461125)*(H/3)*(1-H/3-D/3-s/3) +
    2*(H/3)*(s/3) +
    (13368979/8217000)*(H/3)*(D/3) +
    (3139883/4108500)*(H/3)^2

private theorem upperP1_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP1 H D s := by
  unfold upperP1
  positivity

private def upperP2 (H D s : ℝ) : ℝ :=
  (20097793/83813400)*(1-H/3-D/3-s/3)^2 +
    (78556/3492225)*(s/3)*(1-H/3-D/3-s/3) +
    (914639113/7459392600)*(D/3)*(1-H/3-D/3-s/3) +
    (163/1826)*(D/3)^2 +
    (166244893/209533500)*(H/3)*(1-H/3-D/3-s/3) +
    (20300639/82170000)*(H/3)*(D/3) +
    (968617/4108500)*(H/3)^2

private theorem upperP2_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP2 H D s := by
  unfold upperP2
  positivity

private def upperP3 (H D s : ℝ) : ℝ :=
  (105622307/125720100)*(1-H/3-D/3-s/3)^2 +
    (1082666/10476675)*(s/3)*(1-H/3-D/3-s/3) +
    (2389/136950)*(s/3)^2 +
    (2253002359/2237817780)*(D/3)*(1-H/3-D/3-s/3) +
    (3581/45650)*(D/3)*(s/3) +
    (34472/68475)*(D/3)^2 +
    (7613081/12572010)*(H/3)*(1-H/3-D/3-s/3) +
    (6418669/30813750)*(H/3)*(D/3) +
    (968617/12325500)*(H/3)^2

private theorem upperP3_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP3 H D s := by
  unfold upperP3
  positivity

private def upperP4 (H D s : ℝ) : ℝ :=
  (56690239709/74593926000)*(1-H/3-D/3-s/3)^2 +
    (5619805903/74593926000)*(s/3)*(1-H/3-D/3-s/3) +
    (86808773/89872200)*(D/3)*(1-H/3-D/3-s/3) +
    (3581/45650)*(D/3)*(s/3) +
    (21623/45650)*(D/3)^2 +
    (71469719/209533500)*(H/3)*(1-H/3-D/3-s/3)

private theorem upperP4_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP4 H D s := by
  unfold upperP4
  positivity

private def upperP5 (H D s : ℝ) : ℝ :=
  (16650521/74593926000)*(1-H/3-D/3-s/3)^2 +
    (509819099/24864642000)*(s/3)*(1-H/3-D/3-s/3) +
    (2389/136950)*(s/3)^2 +
    (3449857/27390000)*(H/3)*(D/3)

private theorem upperP5_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP5 H D s := by
  unfold upperP5
  positivity

private def upperP6 (H D s : ℝ) : ℝ :=
  0

private theorem upperP6_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP6 H D s := by
  unfold upperP6
  positivity

private def upperP7 (H D s : ℝ) : ℝ :=
  0

private theorem upperP7_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperP7 H D s := by
  unfold upperP7
  positivity

private def upperResidual (H D s : ℝ) : ℝ :=
  (534407/3880250)*(s/3)^3*(1-H/3-D/3-s/3) +
    (2529/22825)*(s/3)^4 +
    (13746167051/24864642000)*(D/3)*(1-H/3-D/3-s/3)^3 +
    (12634789237/24864642000)*(D/3)*(s/3)^2*(1-H/3-D/3-s/3) +
    (33778451/11640750)*(H/3)*(1-H/3-D/3-s/3)^3 +
    (3022109/11640750)*(H/3)*(s/3)*(1-H/3-D/3-s/3)^2 +
    (102332/114125)*(H/3)*(s/3)^3 +
    (114686254171/12432321000)*(H/3)*(D/3)*(1-H/3-D/3-s/3)^2 +
    (7224369401/4972928400)*(H/3)*(D/3)*(s/3)*(1-H/3-D/3-s/3) +
    (28683757/68475000)*(H/3)*(D/3)*(s/3)^2 +
    (424760691607/62161605000)*(H/3)*(D/3)^2*(1-H/3-D/3-s/3) +
    (7112797/6847500)*(H/3)*(D/3)^2*(s/3) +
    (17283557/17118750)*(H/3)*(D/3)^3 +
    (2880137/3423750)*(H/3)^2*(s/3)^2 +
    (2682007263/690684500)*(H/3)^2*(D/3)*(1-H/3-D/3-s/3) +
    (79081/136950)*(H/3)^3*(s/3) +
    (229911241/136950000)*(H/3)^3*(D/3) +
    (1249973/3423750)*(H/3)^4

private theorem upperResidual_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/3-D/3-s/3) :
    0 ≤ upperResidual H D s := by
  unfold upperResidual
  positivity

private theorem upper_identity (r H D a q s : ℝ) (hm : H+D+s=5-10*r) :
    B r-W r H D a q = upperP1 H D s*(4-a-q-2*r*H-10*r^2) +
    upperP2 H D s*(4*s-(2/5)*s^2-(2/3)*(a-H^2/10)-(q-D^2/15)) +
    upperP3 H D s*(H^2-a) +
    upperP4 H D s*(D-q) +
    upperP5 H D s*(D^2-q) +
    upperP6 H D s*(a-H^2/9) +
    upperP7 H D s*(q-D^2/14) + upperResidual H D s := by
  have hr : r=(5-H-D-s)/10 := by linarith
  rw [hr]
  unfold B W upperP1 upperP2 upperP3 upperP4 upperP5 upperP6 upperP7 upperResidual
  ring

theorem upper_certificate {r H D a q s : ℝ} (h : Hyp r H D a q s)
    (hr : 1/5 ≤ r) : W r H D a q ≤ B r := by
  have hw : 0 ≤ 1-H/3-D/3-s/3 := by linarith [h.mass]
  have he := (energy_envelopes h)

  have hg1 : 0 ≤ 4-a-q-2*r*H-10*r^2 := by linarith [he.2]

  have ht1 := mul_nonneg (upperP1_nonneg H D s h.H0 h.D0 h.s0 hw) hg1

  have hg2 : 0 ≤ 4*s-(2/5)*s^2-(2/3)*(a-H^2/10)-(q-D^2/15) := by linarith [h.variance]

  have ht2 := mul_nonneg (upperP2_nonneg H D s h.H0 h.D0 h.s0 hw) hg2

  have hg3 : 0 ≤ H^2-a := by linarith [h.amax]

  have ht3 := mul_nonneg (upperP3_nonneg H D s h.H0 h.D0 h.s0 hw) hg3

  have hg4 : 0 ≤ D-q := by linarith [h.qbox]

  have ht4 := mul_nonneg (upperP4_nonneg H D s h.H0 h.D0 h.s0 hw) hg4

  have hg5 : 0 ≤ D^2-q := by linarith [h.qmass]

  have ht5 := mul_nonneg (upperP5_nonneg H D s h.H0 h.D0 h.s0 hw) hg5

  have hg6 : 0 ≤ a-H^2/9 := by linarith [h.amin]

  have ht6 := mul_nonneg (upperP6_nonneg H D s h.H0 h.D0 h.s0 hw) hg6

  have hg7 : 0 ≤ q-D^2/14 := by linarith [h.qmin]

  have ht7 := mul_nonneg (upperP7_nonneg H D s h.H0 h.D0 h.s0 hw) hg7

  have hres := upperResidual_nonneg H D s h.H0 h.D0 h.s0 hw

  have hid := upper_identity r H D a q s h.mass

  linarith only [hid,hres,ht1,ht2,ht3,ht4,ht5,ht6,ht7]

private def smallqP1 (H D s : ℝ) : ℝ :=
  (30033956315/65357462512)*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (1396804422865/1176434325216)*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (33458255/38958219)*(s/(25/6))^2 +
    (498202861635299545/369299204765855424)*(D/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    2*(D/(25/6))*(s/(25/6)) +
    (200051939855/252527175558)*(D/(25/6))^2 +
    (14804538611845/9411474601728)*(H/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (218915/114921)*(H/(25/6))*(s/(25/6)) +
    (372457465/212833692)*(H/(25/6))*(D/(25/6)) +
    (110/113)*(H/(25/6))^2

private theorem smallqP1_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP1 H D s := by
  unfold smallqP1
  positivity

private def smallqP2 (H D s : ℝ) : ℝ :=
  (51192155843/261429850048)*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (1698653624519/4705737300864)*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (12622166359/55524923904)*(H/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (2547001/10463800)*(H/(25/6))*(D/(25/6))

private theorem smallqP2_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP2 H D s := by
  unfold smallqP2
  positivity

private def smallqP3 (H D s : ℝ) : ℝ :=
  (160748881339/392144775072)*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (4037731740883/7058605951296)*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (5499964/38958219)*(s/(25/6))^2 +
    (240395547896411303/369299204765855424)*(D/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (52475235703/252527175558)*(D/(25/6))^2 +
    (216008816087/784289550144)*(H/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (10927/114921)*(H/(25/6))*(s/(25/6)) +
    (116703659/1330210575)*(H/(25/6))*(D/(25/6)) +
    (3/113)*(H/(25/6))^2

private theorem smallqP3_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP3 H D s := by
  unfold smallqP3
  positivity

private def smallqP4 (H D s : ℝ) : ℝ :=
  0

private theorem smallqP4_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP4 H D s := by
  unfold smallqP4
  positivity

private def smallqP5 (H D s : ℝ) : ℝ :=
  0

private theorem smallqP5_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP5 H D s := by
  unfold smallqP5
  positivity

private def smallqP6 (H D s : ℝ) : ℝ :=
  0

private theorem smallqP6_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP6 H D s := by
  unfold smallqP6
  positivity

private def smallqP7 (H D s : ℝ) : ℝ :=
  (344134997141/784289550144)*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (78374909/155832876)*(s/(25/6))^2 +
    (533026393320253423/1477196819063421696)*(D/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (3/2)*(D/(25/6))*(s/(25/6)) +
    (55750696679/144301243176)*(D/(25/6))^2 +
    (36897802260493/37645898406912)*(H/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (613037/459684)*(H/(25/6))*(s/(25/6)) +
    (27793918009/21283369200)*(H/(25/6))*(D/(25/6)) +
    (159/226)*(H/(25/6))^2

private theorem smallqP7_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP7 H D s := by
  unfold smallqP7
  positivity

private def smallqP8 (H D s : ℝ) : ℝ :=
  0

private theorem smallqP8_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP8 H D s := by
  unfold smallqP8
  positivity

private def smallqP9 (H D s : ℝ) : ℝ :=
  (150169781575/65357462512)*(1-H/(25/6)-D/(25/6)-s/(25/6))^2

private theorem smallqP9_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqP9 H D s := by
  unfold smallqP9
  positivity

private def smallqResidual (H D s : ℝ) : ℝ :=
  (31808613506875/21175817853888)*(s/(25/6))^3*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (817203125/1402495884)*(s/(25/6))^4 +
    (230854760254119965/246199469843903616)*(D/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6))^3 +
    (14358263135826312353/2215795228595132544)*(D/(25/6))*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (95232099718922235737/26589542743141590528)*(D/(25/6))*(s/(25/6))^2*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (2450689901/2804991768)*(D/(25/6))*(s/(25/6))^3 +
    (65776222538703920395/31021133200331855616)*(D/(25/6))^2*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (45123507597497050943/6647385685785397632)*(D/(25/6))^2*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (40740632502233/36363913280352)*(D/(25/6))^2*(s/(25/6))^2 +
    (626149662030456809785/248169065602654844928)*(D/(25/6))^3*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (46602266514887/18181956640176)*(D/(25/6))^3*(s/(25/6)) +
    (23671217362945/24242608853568)*(D/(25/6))^4 +
    (5262949710625/2091438800384)*(H/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6))^3 +
    (366761424299375/56468847610368)*(H/(25/6))*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (3778091816391875/677626171324416)*(H/(25/6))*(s/(25/6))^2*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (287328125/155832876)*(H/(25/6))*(s/(25/6))^3 +
    (25941300685492426495/2954393638126843392)*(H/(25/6))*(D/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6))^2 +
    (235879301190018920699/17726361828761060352)*(H/(25/6))*(D/(25/6))*(s/(25/6))*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (409078796053/577204972704)*(H/(25/6))*(D/(25/6))*(s/(25/6))^2 +
    (1031248283135213392835/110297362490068819968)*(H/(25/6))*(D/(25/6))^2*(1-H/(25/6)-D/(25/6)-s/(25/6)) +
    (8689697623633/12121304426784)*(H/(25/6))*(D/(25/6))^2*(s/(25/6)) +
    (156425983608905/48485217707136)*(H/(25/6))*(D/(25/6))^3

private theorem smallqResidual_nonneg (H D s : ℝ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hs : 0 ≤ s) (hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6)) :
    0 ≤ smallqResidual H D s := by
  unfold smallqResidual
  positivity

private theorem smallq_identity (r H D a q s : ℝ) (hm : H+D+s=5-10*r) :
    B r-W r H D a q = smallqP1 H D s*(4-a-(7/4)*q-2*r*H-10*r^2) +
    smallqP2 H D s*(4*s-(2/5)*s^2-(2/3)*(a-H^2/10)-(q-D^2/15)) +
    smallqP3 H D s*(H^2-a) +
    smallqP4 H D s*(D-q) +
    smallqP5 H D s*(D^2-q) +
    smallqP6 H D s*(a-H^2/9) +
    smallqP7 H D s*(q-D^2/14) +
    smallqP8 H D s*(1-q) +
    smallqP9 H D s*(1/5-r) + smallqResidual H D s := by
  have hr : r=(5-H-D-s)/10 := by linarith
  rw [hr]
  unfold B W smallqP1 smallqP2 smallqP3 smallqP4 smallqP5 smallqP6 smallqP7 smallqP8 smallqP9 smallqResidual
  ring

theorem smallq_certificate {r H D a q s : ℝ} (h : Hyp r H D a q s)
    (hr : 1/12 ≤ r) (hr' : r ≤ 1/5) (hq : q ≤ 1) : W r H D a q ≤ B r := by
  have hw : 0 ≤ 1-H/(25/6)-D/(25/6)-s/(25/6) := by linarith [h.mass]
  have he := (energy_envelopes h)

  have hqprod := mul_nonneg h.q0 (show 0 ≤ 1-q by linarith)

  have hg1 : 0 ≤ 4-a-(7/4)*q-2*r*H-10*r^2 := by
    dsimp [phi] at he
    nlinarith [he.1]

  have ht1 := mul_nonneg (smallqP1_nonneg H D s h.H0 h.D0 h.s0 hw) hg1

  have hg2 : 0 ≤ 4*s-(2/5)*s^2-(2/3)*(a-H^2/10)-(q-D^2/15) := by linarith [h.variance]

  have ht2 := mul_nonneg (smallqP2_nonneg H D s h.H0 h.D0 h.s0 hw) hg2

  have hg3 : 0 ≤ H^2-a := by linarith [h.amax]

  have ht3 := mul_nonneg (smallqP3_nonneg H D s h.H0 h.D0 h.s0 hw) hg3

  have hg4 : 0 ≤ D-q := by linarith [h.qbox]

  have ht4 := mul_nonneg (smallqP4_nonneg H D s h.H0 h.D0 h.s0 hw) hg4

  have hg5 : 0 ≤ D^2-q := by linarith [h.qmass]

  have ht5 := mul_nonneg (smallqP5_nonneg H D s h.H0 h.D0 h.s0 hw) hg5

  have hg6 : 0 ≤ a-H^2/9 := by linarith [h.amin]

  have ht6 := mul_nonneg (smallqP6_nonneg H D s h.H0 h.D0 h.s0 hw) hg6

  have hg7 : 0 ≤ q-D^2/14 := by linarith [h.qmin]

  have ht7 := mul_nonneg (smallqP7_nonneg H D s h.H0 h.D0 h.s0 hw) hg7

  have hg8 : 0 ≤ 1-q := by linarith

  have ht8 := mul_nonneg (smallqP8_nonneg H D s h.H0 h.D0 h.s0 hw) hg8

  have hg9 : 0 ≤ 1/5-r := by linarith

  have ht9 := mul_nonneg (smallqP9_nonneg H D s h.H0 h.D0 h.s0 hw) hg9

  have hres := smallqResidual_nonneg H D s h.H0 h.D0 h.s0 hw

  have hid := smallq_identity r H D a q s h.mass

  linarith only [hid,hres,ht1,ht2,ht3,ht4,ht5,ht6,ht7,ht8,ht9]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP2Certificates
