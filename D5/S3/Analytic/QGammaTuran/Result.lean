/- GID: D5/S3/Analytic/QGammaTuran/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/QGammaTuran/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Summable]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/QGammaTuran/Result.claim; result=D5/S3/Analytic/QGammaTuran/Result.result; claim=D5/S3/Analytic/QGammaTuran/Result.claim
   digest: An exact infinite-product counterexample to q-gamma Turanian coefficient positivity. -/

/-
admission_basis: open-problem-resolution (Conjecture 1, coefficient clause; Refuted).
Per-declaration judgment (generated constant dependencies, same-delivery helpers inlined):
* rqgamma: proof_shape: bind-only (definition); escape_witness: none; consumers: qturanCoeff, result.
* qturanCoeff: proof_shape: bind-only (definition); escape_witness: none; consumers: claim, result.
* qprod: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
* checkLower: proof_shape: bind-only (definition); escape_witness: none; consumers: instDecidableCheckLower, result.
* instDecidableCheckLower: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
* checkUpper: proof_shape: bind-only (definition); escape_witness: none; consumers: instDecidableCheckUpper, result.
* instDecidableCheckUpper: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
* lower3: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
* lower7: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
* upperQ: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
* r: proof_shape: bind-only (definition); escape_witness: none; consumers: q, result.
* q: proof_shape: bind-only (definition); escape_witness: none; consumers: bracket, result.
* bracket: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
  Direct frozen D5 dependencies of all preceding declarations: none.
* claim: proof_shape: bind-only (definition); escape_witness: none; consumer: result.
  Direct frozen D5 dependency:
  GID D5/S3/Analytic/ReciprocalGammaTuran/Defs.AdmissibleSeq
  declaration statement_id sha256:abfc032d4781455ce9be9b5d79eeec0ec7d429144bd78d17dfed678546f63347.
* result: proof_shape: content; escape_witness: result (lowerSound/upperSound rounded-state product enclosures); consumer: the coefficient clause's refutation.
  Direct frozen D5 dependencies:
  GID D5/S3/Analytic/ReciprocalGammaTuran/Defs.AdmissibleSeq
  declaration statement_id sha256:abfc032d4781455ce9be9b5d79eeec0ec7d429144bd78d17dfed678546f63347;
  GID D5/S3/Analytic/ReciprocalGammaTuran/Defs.admissible_one
  declaration statement_id sha256:542b2ef036086b557abca79ec9fd79a7a609bad51893576abe9466237f76c069;
  GID D5/S3/Factorization/JordanCototientRecordLimitInfinity.one_sub_prod_le_sum
  declaration statement_id sha256:2ae9c4b59c9a8107bcc321a08d511c7f7b3dbfd7742469936401e2f244f3e6bd.
The local lowerSound and upperSound inductions establish rounded-state product
invariants. The remaining product bounds, recurrences and coefficient reduction
reuse frozen and Mathlib inequalities. The escape witness is the lowerSound/upperSound
rounded-state product induction, used by qprod_numeric and witness_negative to
establish strict negativity. Instantiation and normalization of upstream facts
do not supply these certificate-state invariants or their numerical enclosures;
they remain a genuine estimate on the proof path after the upstream-only bypass.
-/

import D5.S3.Analytic.ReciprocalGammaTuran.Defs
import D5.S3.Factorization.JordanCototientRecordLimitInfinity
import Mathlib.Analysis.SpecialFunctions.Log.Summable

noncomputable section
open scoped BigOperators
open Filter
open D5.S3.Analytic.ReciprocalGammaTuran.Defs
set_option maxHeartbeats 2000000
namespace D5.S3.Analytic.QGammaTuran.Result

/-- Reciprocal q-gamma, extended by zero at its poles. -/
def rqgamma (q x : ℝ) : ℝ :=
  (∏' j : ℕ, (1 - q ^ (x + j))) /
    ((∏' j : ℕ, (1 - q ^ ((j : ℝ) + 1))) * (1 - q) ^ (1 - x))

/-- The degree m Cauchy coefficient of the shifted Turanian. -/
def qturanCoeff (q : ℝ) (g : ℕ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m+1), g k * g (m-k) *
    (rqgamma q ((k:ℝ)+μ+α) * rqgamma q (((m-k:ℕ):ℝ)+μ+β) -
      rqgamma q ((k:ℝ)+μ) * rqgamma q (((m-k:ℕ):ℝ)+μ+α+β))

def qprod (q a : ℝ) : ℝ := ∏' j : ℕ, (1 - a * q ^ j)

private def checkLower (d b : ℕ) (s : ℕ × ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | t :: ts => s.1 ≤ d ∧ s.1 * b ≤ t.1 * d ∧
      t.2 * d ≤ s.2 * (d-s.1) ∧ checkLower d b t ts

private instance (d b : ℕ) (s : ℕ × ℕ) (ts : List (ℕ × ℕ)) :
    Decidable (checkLower d b s ts) := by
  induction ts generalizing s with
  | nil => exact isTrue trivial
  | cons t ts ih => unfold checkLower; exact instDecidableAnd

private def checkUpper (d b : ℕ) (s : ℕ × ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | t :: ts => s.1 ≤ d ∧ t.1 * d ≤ s.1 * b ∧
      s.2 * (d-s.1) ≤ t.2 * d ∧ checkUpper d b t ts

private instance (d b : ℕ) (s : ℕ × ℕ) (ts : List (ℕ × ℕ)) :
    Decidable (checkUpper d b s ts) := by
  induction ts generalizing s with
  | nil => exact isTrue trivial
  | cons t ts ih => unfold checkUpper; exact instDecidableAnd

private def lower3 : List (ℕ × ℕ) := [
  (87752102299896798786, 2970100000000000000),
  (79361428364365551680, 363774809590765179),
  (71773053259827510591, 75077924669782884),
  (64910262836840243301, 21192205810166437),
  (58703678193748467441, 7436289317863273),
  (53090554295511346961, 3070913967148724),
  (48014145657142150406, 1440548720051189),
  (43423132679181196620, 748881559343714),
  (39271102835780518439, 423693726219972),
  (35516081470507331544, 257304527287376),
  (32120107456479172789, 165920041748687),
  (29048849430996407647, 112626346047173),
  (26271258725022860770, 79909688364296),
  (23759255478829334281, 58916407387752),
  (21487444770607980036, 44918307637548),
  (19432859888279529990, 35266511092038),
  (17574730149117605934, 28413219404037),
  (15894270919978776410, 23419672767100),
  (14374493715362505716, 19697286528924),
  (13000034453500562383, 16865901314726),
  (11756998134242788296, 14673328332918),
  (10632818368521135806, 12948185394585),
  (9616130339314876025, 11571428359559),
  (8696655909824706782, 10458704726383),
  (7865099717364850826, 9549147163704),
  (7113055202541585514, 8798097217120),
  (6432919623726731205, 8172283705292),
  (5817817197670838977, 7646567263107),
  (5261529589251461435, 7201703957842),
  (4758433047647459475, 6822784173169),
  (4303441553421878845, 6498126556303),
  (3891955401762791749, 6218483477885),
  (3519814702087958943, 5976462874259),
  (3183257323920805315, 5766102455346),
  (2878880863894472004, 5582552576631),
  (2603608249392022250, 5421837538785),
  (2354656631095198014, 5280674129356),
  (2129509249963116254, 5156332385802),
  (1925889994232085995, 5046527810687),
  (1741740389222308443, 4949337236524),
  (1575198787331514082, 4863132630876),
  (1424581547838227241, 4786528624648),
  (1288366016253190431, 4718340621079),
  (1165175131149887494, 4657551123985),
  (1053763502857991161, 4603282496567),
  (953004823283256327, 4554774785684),
  (861880479574310392, 4511367562286),
  (779469256526998368, 4472484965904),
  (704938023623456907, 4437623320591),
  (637533312557187597, 4406340826458),
  (576573700097706031, 4378248935824),
  (521442919289867521, 4353005103935),
  (471583629346018955, 4330306667044),
  (426491781248135569, 4309885649701),
  (385711522099389979, 4291504341623),
  (348830586711050659, 4274951514905),
  (315476129836278696, 4260039176453),
  (285310956917080744, 4246599769729)]

private def lower7 : List (ℕ × ℕ) := [
  (84294319338392688325, 6793465209301000000),
  (76234271434710375125, 1066959951630207837),
  (68944908586907799961, 253570806004780668),
  (62352539489120018722, 78746645601699321),
  (56390519045238784767, 29646112306542359),
  (50998574624956560800, 12928515700148710),
  (46122196741809577682, 6335156972909144),
  (41712087993322067540, 3413243409961520),
  (37723664692350451248, 1989508315372104),
  (34116606151404275356, 1238992869454701),
  (30854447063465142029, 816290551938858),
  (27904208858505919510, 564428615706815),
  (25236066308934647215, 406929275922811),
  (22823046013534097982, 304236334020462),
  (20640753711741390897, 234800335517082),
  (18667127671570362273, 186335776548658),
  (16882215658069077281, 151552239242507),
  (15267973227590641904, 125966863378954),
  (13808081308747298694, 106734276402619),
  (12487781225895170758, 91996320732642),
  (11293725497331066808, 80508021463676),
  (10213842899856112656, 71415666516236),
  (9237216435585816044, 64121382532382),
  (8353972967320533135, 58198351646375),
  (7555183406752803419, 53336477082410),
  (6832772446471188905, 49306808416133),
  (6179436923202599327, 45937786396441),
  (5588571986991989216, 43099089862157),
  (5054204329931892742, 40690466199471),
  (4570931799422289459, 38633886894947),
  (4133868785485258666, 36867958273513),
  (3738596830031284721, 35343885254598),
  (3381119958765032030, 34022519880859),
  (3057824284161603142, 32872177670692),
  (2765441471122382869, 31867004239144),
  (2501015695969061500, 30985740888310),
  (2261873764750089143, 30210782645181),
  (2045598088772662121, 29527452878403),
  (1850002244158264821, 28923439866659),
  (1673108868342796494, 28388355580038),
  (1513129670067490975, 27913387485251),
  (1368447350773025214, 27491021737290),
  (1237599254632409879, 27114821578625),
  (1119262581933808639, 26779248748873),
  (1012241016329009906, 26479518637903),
  (915452630756651128, 26211482089323),
  (827918949775969061, 25971528386975),
  (748755057737501089, 25756505181912),
  (677160652789978447, 25563652046666),
  (612411956284517302, 25390545053589),
  (553854395784793023, 25235050319915),
  (500895987712598774, 25095284884439),
  (453001352731104717, 24969583609347),
  (409686303364751847, 24856471057825),
  (370512949139700837, 24754637500401),
  (335085269760594286, 24662918362949),
  (303045111570971269, 24580276556421),
  (274068566823829664, 24505787229906)]

private def upperQ : List (ℕ × ℕ) := [
  (81790693759723087088, 9561792499119550999),
  (73970037338828042272, 1741136078224506184),
  (66897175856968051392, 453217071042032730),
  (60500606713753665043, 150027650013244269),
  (54715664239076147617, 59260011516844556),
  (49483865960020725984, 26835502587250033),
  (44752321376381091411, 13556258457277333),
  (40473197267832408807, 7489518105863740),
  (36603234127322950490, 4458270668467484),
  (33103308832101416968, 2826399417658565),
  (29938039131233163839, 1890767689602335),
  (27075425951199435187, 1324708918808475),
  (24486529903492979250, 966038336427552),
  (22145178723886121729, 729489070299014),
  (20027702685748959837, 567942411910083),
  (18112695312597050934, 454196594226460),
  (16380796970808767607, 371929348994029),
  (14814499154757972239, 311004357460467),
  (13397967485796195166, 264930619553226),
  (12116881635704858282, 229435301285567),
  (10958290556334836783, 201634897398273),
  (9910481551887486244, 179539159478403),
  (8962861870232481711, 161745964199883),
  (8105851616218145969, 147248896847972),
  (7330786904388838393, 135313119762958),
  (6629832272038548112, 125393603299456),
  (5995901467146558913, 117080217720837),
  (5422585810406340133, 110060203228775),
  (4904089407128585585, 104092094265588),
  (4435170554047648029, 98987324897051),
  (4011088748687560988, 94597068210978),
  (3627556765582525523, 90802695851380),
  (3280697314869751803, 87508776514692),
  (2967003845097719357, 84637878433300),
  (2683305093988576965, 82126669325775),
  (2426733028783084394, 79922960224234),
  (2194693852063246735, 77983443350892),
  (1984841779938025273, 76271945514043),
  (1795055327504520187, 74758068073109),
  (1623415861844147085, 73416119389424),
  (1468188205736816416, 72224270462106),
  (1327803096007715582, 71163882241502),
  (1200841319170572663, 70218966009861),
  (1086019363987792579, 69375747652121),
  (982176445903021973, 68622313598708),
  (888262772170547823, 67948321397908),
  (803328929048672994, 67344761754616),
  (726516283767639559, 66803761801243),
  (657048304241463287, 66318421593588),
  (594222708770910843, 65882677529108),
  (537404366375588875, 65491187698084),
  (486018875981546867, 65139235195804),
  (439546759553638165, 64822646217083),
  (397518210468515342, 64537720376179),
  (359508344037302572, 64281171185063),
  (325132902163434865, 64050075011008),
  (294044368712201841, 63841827143287),
  (265928456320595089, 63654103845690)]

private def r : ℝ := 99/100

private def q : ℝ := r^10

private def bracket (x : ℝ) : ℝ := (1-q^x)/(1-q)

/-- The coefficient clause of Conjecture 1, with every parameter restriction retained. -/
def claim : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ g : ℕ → ℝ, AdmissibleSeq g →
    ∀ μ α β : ℝ, 0 < α → 0 < β → max (-β) (-1) ≤ μ → α ≤ β+1 →
      ∀ m : ℕ, 0 < qturanCoeff q g μ α β m

/-- Conjecture 1's universal coefficient positivity clause is false. -/
theorem result : ¬ claim := by
  have qprod_multipliable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
      Multipliable (fun j : ℕ => 1 - a * q ^ j) := by
    simpa only [sub_eq_add_neg, neg_mul] using
      Real.multipliable_one_add_of_summable
        ((summable_geometric_of_lt_one hq0 hq1).mul_left (-a))

  have qprod_step {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
      qprod q a = (1 - a) * qprod q (a*q) := by
    unfold qprod
    have htail : Multipliable (fun j : ℕ => 1 - a * q^(j+1)) := by
      convert qprod_multipliable hq0 hq1 (a*q) using 1
      ext j
      rw [pow_succ]
      ring
    rw [tprod_eq_zero_mul' htail]
    simp only [pow_zero, mul_one]
    congr 1
    apply tprod_congr
    intro j
    rw [pow_succ]
    ring

  have qprod_nonneg {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
      (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ qprod q a := by
    unfold qprod
    exact tprod_nonneg fun i => sub_nonneg.mpr
      (by nlinarith [pow_le_one₀ hq0 hq1.le (n := i)] : a*q^i ≤ 1)

  have qprod_ne_zero {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
      (ha0 : 0 ≤ a) (ha1 : a < 1) : qprod q a ≠ 0 := by
    unfold qprod
    have hs : Summable (fun j : ℕ => ‖- (a * q^j)‖) := by
      simpa only [norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha0 (pow_nonneg hq0 _))]
        using (summable_geometric_of_lt_one hq0 hq1).mul_left a
    have hn (j : ℕ) : 1 + -(a * q^j) ≠ 0 := by
      have h : a*q^j < 1 := by nlinarith [pow_le_one₀ hq0 hq1.le (n := j)]
      linarith
    simpa only [sub_eq_add_neg] using tprod_one_add_ne_zero_of_summable hn hs

  have qprod_pos {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
      (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < qprod q a :=
    lt_of_le_of_ne (qprod_nonneg hq0 hq1 ha0 ha1.le) (qprod_ne_zero hq0 hq1 ha0 ha1).symm

  have qprod_le_one {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
      (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : qprod q a ≤ 1 := by
    apply (qprod_multipliable hq0 hq1 a).tprod_le_of_prod_range_le
    intro n
    exact Finset.prod_le_one₀
      (fun i _ => sub_nonneg.mpr (by nlinarith [pow_le_one₀ hq0 hq1.le (n := i)]))
      (fun i _ => sub_le_self _ (mul_nonneg ha0 (pow_nonneg hq0 _)))

  have qprod_lower {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
      (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 1 - a / (1-q) ≤ qprod q a := by
    have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left a
    have hp := (qprod_multipliable hq0 hq1 a).hasProd.tendsto_prod_nat
    have hsum := hs.hasSum.tendsto_sum_nat
    have hfinite (n : ℕ) : 1 - ∑ i ∈ Finset.range n, a*q^i ≤ ∏ i ∈ Finset.range n, (1-a*q^i) := by
      have h := D5.S3.Factorization.JordanCototientRecordLimitInfinity.one_sub_prod_le_sum
        (Finset.range n) (fun i => a*q^i)
        (fun i _ => mul_nonneg ha0 (pow_nonneg hq0 i))
        (fun i _ => by nlinarith [pow_le_one₀ hq0 hq1.le (n := i)])
      linarith

    have h := le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub hsum) hp hfinite
    simpa only [qprod, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv] using h

  have qprod_split {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) (n : ℕ) :
      qprod q a = (∏ j ∈ Finset.range n, (1-a*q^j)) * qprod q (a*q^n) := by
    have ht : Multipliable (fun j : ℕ => 1-a*q^(j+n)) := by
      convert qprod_multipliable hq0 hq1 (a*q^n) using 1
      ext j
      rw [pow_add]
      ring
    rw [qprod, ← ht.prod_mul_tprod_nat_mul']
    congr 1
    apply tprod_congr
    intro j
    simp only [pow_add]
    ring

  have qprod_bounds {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
      (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
      (∏ j ∈ Finset.range n, (1-a*q^j)) * (1-a*q^n/(1-q)) ≤ qprod q a ∧
      qprod q a ≤ ∏ j ∈ Finset.range n, (1-a*q^j) := by
    have ht0 := mul_nonneg ha0 (pow_nonneg hq0 n)
    have ht1 : a*q^n ≤ 1 := by nlinarith [pow_le_one₀ hq0 hq1.le (n := n)]
    have hp0 : 0 ≤ ∏ j ∈ Finset.range n, (1-a*q^j) :=
      Finset.prod_nonneg fun j _ => sub_nonneg.mpr
        (by nlinarith [pow_le_one₀ hq0 hq1.le (n := j)])
    rw [qprod_split hq0 hq1 a n]
    exact ⟨mul_le_mul_of_nonneg_left (qprod_lower hq0 hq1 ht0 ht1) hp0,
      (mul_le_mul_of_nonneg_left (qprod_le_one hq0 hq1 ht0 ht1) hp0).trans_eq (mul_one _)⟩

  have lowerSound (d b : ℕ) (hd : 0 < d) (q a : ℝ)
      (hq : q = (b:ℝ)/d) (ha : 0 ≤ a) (hq0 : 0 ≤ q)
      (s : ℕ × ℕ) (ts : List (ℕ × ℕ)) (hc : checkLower d b s ts)
      (n : ℕ) (hx : a*q^n ≤ (s.1:ℝ)/d)
      (hy : (s.2:ℝ)/d ≤ ∏ j ∈ Finset.range n, (1-a*q^j)) :
      a*q^(n+ts.length) ≤ ((ts.getLastD s).1:ℝ)/d ∧
      ((ts.getLastD s).2:ℝ)/d ≤ ∏ j ∈ Finset.range (n+ts.length), (1-a*q^j) := by
    have hd' : (0:ℝ) < d := Nat.cast_pos'.mpr hd
    induction ts generalizing n s with
    | nil => simpa using And.intro hx hy
    | cons t ts ih =>
      rcases hc with ⟨hs, hxt, hyt, hc⟩
      have hs' : (s.1:ℝ) ≤ d := Nat.cast_le.mpr hs
      have hxt' : (s.1:ℝ)*b ≤ (t.1:ℝ)*d := by exact_mod_cast hxt
      have hyt' : (t.2:ℝ)*d ≤ (s.2:ℝ)*(d-s.1) := by
        exact_mod_cast hyt
      have hnon : 0 ≤ 1-a*q^n := by
        have := (div_le_one₀ hd').mpr hs'
        linarith
      have hx' : a*q^(n+1) ≤ (t.1:ℝ)/d := by
        rw [pow_succ]
        calc
          _ = (a*q^n)*q := by ring
          _ ≤ ((s.1:ℝ)/d)*q := mul_le_mul_of_nonneg_right hx hq0
          _ ≤ (t.1:ℝ)/d := by
            rw [hq]
            apply (mul_le_mul_iff_left₀ hd').mp
            apply (mul_le_mul_iff_left₀ hd').mp
            convert hxt' using 1 <;> field_simp <;> ring
      have hy' : (t.2:ℝ)/d ≤ ∏ j ∈ Finset.range (n+1), (1-a*q^j) := by
        rw [Finset.prod_range_succ]
        calc
          _ ≤ ((s.2:ℝ)/d)*(1-(s.1:ℝ)/d) := by
            apply (div_le_iff₀ hd').2
            field_simp
            nlinarith
          _ ≤ ((s.2:ℝ)/d)*(1-a*q^n) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right hy hnon
      have hh := ih t hc (n+1) hx' hy'
      cases ts <;> simpa [List.getLastD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

  have upperSound (d b : ℕ) (hd : 0 < d) (q a : ℝ)
      (hq : q = (b:ℝ)/d) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
      (s : ℕ × ℕ) (ts : List (ℕ × ℕ)) (hc : checkUpper d b s ts)
      (n : ℕ) (hx : (s.1:ℝ)/d ≤ a*q^n)
      (hy : (∏ j ∈ Finset.range n, (1-a*q^j)) ≤ (s.2:ℝ)/d) :
      ((ts.getLastD s).1:ℝ)/d ≤ a*q^(n+ts.length) ∧
      (∏ j ∈ Finset.range (n+ts.length), (1-a*q^j)) ≤ ((ts.getLastD s).2:ℝ)/d := by
    have hd' : (0:ℝ) < d := Nat.cast_pos'.mpr hd
    induction ts generalizing n s with
    | nil => simpa using And.intro hx hy
    | cons t ts ih =>
      rcases hc with ⟨hs, hxt, hyt, hc⟩
      have hs' : (s.1:ℝ) ≤ d := Nat.cast_le.mpr hs
      have hxt' : (t.1:ℝ)*d ≤ (s.1:ℝ)*b := by exact_mod_cast hxt
      have hyt' : (s.2:ℝ)*(d-s.1) ≤ (t.2:ℝ)*d := by exact_mod_cast hyt
      have hnon : 0 ≤ 1-a*q^n := by nlinarith [pow_le_one₀ hq0 hq1 (n := n)]
      have hx' : (t.1:ℝ)/d ≤ a*q^(n+1) := by
        rw [pow_succ]
        calc
          _ ≤ ((s.1:ℝ)/d)*q := by
            rw [hq]
            apply (mul_le_mul_iff_left₀ hd').mp
            apply (mul_le_mul_iff_left₀ hd').mp
            convert hxt' using 1 <;> field_simp <;> ring
          _ ≤ (a*q^n)*q := mul_le_mul_of_nonneg_right hx hq0
          _ = _ := by ring
      have hy' : (∏ j ∈ Finset.range (n+1), (1-a*q^j)) ≤ (t.2:ℝ)/d := by
        rw [Finset.prod_range_succ]
        calc
          _ ≤ ((s.2:ℝ)/d)*(1-a*q^n) := mul_le_mul_of_nonneg_right hy hnon
          _ ≤ ((s.2:ℝ)/d)*(1-(s.1:ℝ)/d) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ _ := by
            apply (le_div_iff₀ hd').2
            field_simp
            nlinarith
      have hh := ih t hc (n+1) hx' hy'
      cases ts <;> simpa [List.getLastD, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

  have qprod_numeric :
      (4119/100000000000:ℝ) ≤ qprod ((99/100:ℝ)^10) ((99/100:ℝ)^3) ∧
      (23803/100000000000:ℝ) ≤ qprod ((99/100:ℝ)^10) ((99/100:ℝ)^7) ∧
      qprod ((99/100:ℝ)^10) ((99/100:ℝ)^10) ≤ (63655/100000000000:ℝ) := by
    let d : ℕ := 100000000000000000000
    let b : ℕ := 90438207500880449001
    let q : ℝ := (b:ℝ)/d
    have hd : 0 < d := Nat.zero_lt_succ 99999999999999999999
    have hq0 : 0 ≤ q := by norm_num [q,b,d]
    have hq1 : q < 1 := by norm_num [q,b,d]
    have hqeq : q = (99/100:ℝ)^10 := by norm_num [q,b,d]
    have h3 := lowerSound d b hd q ((99/100:ℝ)^3) rfl (by positivity) hq0
      (97029900000000000000,d) lower3 (by decide) 0 (by norm_num [d]) (by simp [d])
    change (99/100:ℝ)^3*q^58 ≤ (285310956917080744:ℝ)/d ∧
      (4246599769729:ℝ)/d ≤ ∏ j ∈ Finset.range 58, (1-(99/100:ℝ)^3*q^j) at h3
    have h7 := lowerSound d b hd q ((99/100:ℝ)^7) rfl (by positivity) hq0
      (93206534790699000000,d) lower7 (by decide) 0 (by norm_num [d]) (by simp [d])
    change (99/100:ℝ)^7*q^58 ≤ (274068566823829664:ℝ)/d ∧
      (24505787229906:ℝ)/d ≤ ∏ j ∈ Finset.range 58, (1-(99/100:ℝ)^7*q^j) at h7
    have hu := upperSound d b hd q q rfl hq0 hq1.le hq0 hq1.le
      (b,d) upperQ (by decide) 0 (by simp [q]) (by simp [d])
    change (265928456320595089:ℝ)/d ≤ q*q^58 ∧
      (∏ j ∈ Finset.range 58, (1-q*q^j)) ≤ (63654103845690:ℝ)/d at hu
    have h3tail : 1-(285310956917080744:ℝ)/d/(1-q) ≤ 1-(99/100:ℝ)^3*q^58/(1-q) :=
      sub_le_sub_left (div_le_div_of_nonneg_right h3.1 (sub_nonneg.mpr hq1.le)) 1
    have h7tail : 1-(274068566823829664:ℝ)/d/(1-q) ≤ 1-(99/100:ℝ)^7*q^58/(1-q) :=
      sub_le_sub_left (div_le_div_of_nonneg_right h7.1 (sub_nonneg.mpr hq1.le)) 1
    have h3tail0 : 0 ≤ 1-(285310956917080744:ℝ)/d/(1-q) := by norm_num [q,b,d]
    have h7tail0 : 0 ≤ 1-(274068566823829664:ℝ)/d/(1-q) := by norm_num [q,b,d]
    have h3prod0 : 0 ≤ ∏ j ∈ Finset.range 58, (1-(99/100:ℝ)^3*q^j) :=
      le_trans (by norm_num [d]) h3.2
    have h7prod0 : 0 ≤ ∏ j ∈ Finset.range 58, (1-(99/100:ℝ)^7*q^j) :=
      le_trans (by norm_num [d]) h7.2
    have hb3 := (mul_le_mul h3.2 h3tail h3tail0 h3prod0).trans
      (qprod_bounds hq0 hq1 (by positivity : 0 ≤ (99/100:ℝ)^3) (by norm_num) 58).1
    have hb7 := (mul_le_mul h7.2 h7tail h7tail0 h7prod0).trans
      (qprod_bounds hq0 hq1 (by positivity : 0 ≤ (99/100:ℝ)^7) (by norm_num) 58).1
    have hbq := (qprod_bounds hq0 hq1 hq0 hq1.le 58).2.trans hu.2
    rw [hqeq] at hb3 hb7 hbq
    refine ⟨?_,?_,?_⟩
    · exact (by norm_num [q,b,d] : (4119/100000000000:ℝ) ≤ _).trans hb3
    · exact (by norm_num [q,b,d] : (23803/100000000000:ℝ) ≤ _).trans hb7
    · exact hbq.trans (by norm_num [d])

  have rqgamma_eq {q : ℝ} (hq : 0 < q) (x : ℝ) :
      rqgamma q x = qprod q (q^x) / (qprod q q * (1-q)^(1-x)) := by
    unfold rqgamma
    have hn : (∏' j : ℕ, (1-q^(x+j))) = qprod q (q^x) := by
      unfold qprod
      apply tprod_congr
      intro j
      rw [Real.rpow_add_natCast (ne_of_gt hq)]
    have hd : (∏' j : ℕ, (1-q^((j:ℝ)+1))) = qprod q q := by
      unfold qprod
      apply tprod_congr
      intro j
      rw [Real.rpow_add_one (ne_of_gt hq), Real.rpow_natCast]
      ring
    rw [hn, hd]

  have rqgamma_step {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
      rqgamma q x = ((1-q^x)/(1-q)) * rqgamma q (x+1) := by
    have hqprod := qprod_ne_zero hq0.le hq1 hq0.le hq1
    have hpow : (1-q) ^ (1-x) = (1-q) * (1-q) ^ (1-(x+1)) := by
      calc
        _ = (1-q)^((1:ℝ)+(1-(x+1))) := by congr 1; ring
        _ = (1-q)^(1:ℝ) * (1-q)^(1-(x+1)) :=
          Real.rpow_add (by linarith : 0 < 1-q) _ _
        _ = _ := by rw [Real.rpow_one]
    rw [rqgamma_eq hq0 x, rqgamma_eq hq0 (x+1), hpow,
      qprod_step hq0.le hq1 (q^x), Real.rpow_add_one (ne_of_gt hq0)]
    field_simp

  have qprod_eq_zero_iff {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a : ℝ) :
      qprod q a = 0 ↔ ∃ j : ℕ, a*q^j = 1 := by
    constructor
    · intro h
      by_contra hn
      push Not at hn
      have hs : Summable (fun j : ℕ => ‖-(a*q^j)‖) := by
        simpa only [norm_neg, norm_mul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hq0]
          using (summable_geometric_of_lt_one hq0 hq1).mul_left |a|
      have hneq : ∏' j : ℕ, (1 + -(a*q^j)) ≠ 0 :=
        tprod_one_add_ne_zero_of_summable (fun j => by simpa only [sub_eq_add_neg] using sub_ne_zero.mpr (hn j).symm) hs
      exact hneq (by simpa only [qprod, sub_eq_add_neg] using h)
    · rintro ⟨j, hj⟩
      exact tprod_of_exists_eq_zero ⟨j, by simp [hj]⟩

  have rqgamma_eq_zero_iff {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
      rqgamma q x = 0 ↔ ∃ j : ℕ, x = -(j:ℝ) := by
    have hd : qprod q q * (1-q)^(1-x) ≠ 0 :=
      mul_ne_zero (qprod_ne_zero hq0.le hq1 hq0.le hq1)
        (ne_of_gt (Real.rpow_pos_of_pos (by linarith : 0 < 1-q) _))
    rw [rqgamma_eq hq0, div_eq_zero_iff, or_iff_left hd, qprod_eq_zero_iff hq0.le hq1]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have he : q^(x+(j:ℝ)) = q^(0:ℝ) := by
        rw [Real.rpow_add_natCast (ne_of_gt hq0)]
        simpa only [Real.rpow_zero] using hj
      have hh := (Real.rpow_right_inj hq0 (ne_of_lt hq1)).mp he
      linarith
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      rw [← Real.rpow_add_natCast (ne_of_gt hq0)]
      simp

  have rqgamma_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : rqgamma q 0 = 0 := by
    exact (rqgamma_eq_zero_iff hq0 hq1 0).2 ⟨0, by norm_num⟩

  have rqgamma_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : rqgamma q 1 = 1 := by
    rw [rqgamma_eq hq0]
    norm_num [qprod_ne_zero hq0.le hq1 hq0.le hq1]

  have rqgamma_two {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : rqgamma q 2 = 1 := by
    have h := rqgamma_step hq0 hq1 1
    norm_num [rqgamma_one hq0 hq1, ne_of_gt (show 0<1-q by linarith)] at h
    exact h.symm

  have rqgamma_product {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
      rqgamma q (3/10) * rqgamma q (7/10) =
        qprod q (q^(3/10:ℝ)) * qprod q (q^(7/10:ℝ)) /
          ((qprod q q)^2*(1-q)) := by
    rw [rqgamma_eq hq0, rqgamma_eq hq0]
    norm_num
    rw [div_mul_div_comm]
    have hp : (1-q)^(7/10:ℝ) * (1-q)^(3/10:ℝ) = 1-q := by
      rw [← Real.rpow_add (by linarith : 0 < 1-q)]
      norm_num
    have hd : (qprod q q * (1-q)^(7/10:ℝ)) *
        (qprod q q * (1-q)^(3/10:ℝ)) = (qprod q q)^2 * (1-q) := by
      calc
        _ = (qprod q q)^2 * ((1-q)^(7/10:ℝ) * (1-q)^(3/10:ℝ)) := by ring
        _ = _ := by rw [hp]
    rw [hd]

  have q_pos : 0 < q := by norm_num [q, r]

  have q_lt : q < 1 := by norm_num [q, r]

  have q_power (n : ℕ) : q^((n:ℝ)/10) = r^n := by
    unfold q
    rw [← Real.rpow_natCast r 10, ← Real.rpow_mul (by norm_num [r] : 0 ≤ r)]
    convert Real.rpow_natCast r n using 1; congr 1; ring

  have bracket_pos {x : ℝ} (hx : 0 < x) : 0 < bracket x := by
    unfold bracket
    exact div_pos (sub_pos.mpr (Real.rpow_lt_one q_pos.le q_lt hx)) (sub_pos.mpr q_lt)

  have witness_formula :
      qturanCoeff q (fun _ => 1) (-7/10) (7/10) (7/10) 2 =
        1 - (rqgamma q (3/10) * rqgamma q (7/10)) *
          (bracket (-7/10)/(bracket (7/10)*bracket (17/10)) +
            1/bracket (7/10) + 1/bracket (3/10)) := by
    have h3 := rqgamma_step q_pos q_lt (3/10)
    have h7 := rqgamma_step q_pos q_lt (7/10)
    have h17 := rqgamma_step q_pos q_lt (17/10)
    have hm := rqgamma_step q_pos q_lt (-7/10)
    change rqgamma q (3/10) = bracket (3/10) * rqgamma q (3/10+1) at h3
    change rqgamma q (7/10) = bracket (7/10) * rqgamma q (7/10+1) at h7
    change rqgamma q (17/10) = bracket (17/10) * rqgamma q (17/10+1) at h17
    change rqgamma q (-7/10) = bracket (-7/10) * rqgamma q (-7/10+1) at hm
    norm_num at h3 h7 h17 hm
    have hb3 := ne_of_gt (bracket_pos (x := 3/10) (by norm_num))
    have hb7 := ne_of_gt (bracket_pos (x := 7/10) (by norm_num))
    have hb17 := ne_of_gt (bracket_pos (x := 17/10) (by norm_num))
    have he3 : rqgamma q (13/10) = rqgamma q (3/10)/bracket (3/10) := by
      apply (eq_div_iff hb3).2
      simpa [mul_comm] using h3.symm
    have he7 : rqgamma q (17/10) = rqgamma q (7/10)/bracket (7/10) := by
      apply (eq_div_iff hb7).2
      simpa [mul_comm] using h7.symm
    have he17 : rqgamma q (27/10) = rqgamma q (7/10)/(bracket (7/10)*bracket (17/10)) := by
      apply (eq_div_iff (mul_ne_zero hb7 hb17)).2
      rw [h7, h17]
      ring
    norm_num [qturanCoeff, Finset.sum_range_succ, rqgamma_zero q_pos q_lt,
      rqgamma_one q_pos q_lt, rqgamma_two q_pos q_lt]
    rw [hm, he3, he17, he7]
    ring

  have bracket_bound : (397/100:ℝ) <
      bracket (-7/10)/(bracket (7/10)*bracket (17/10)) +
        1/bracket (7/10) + 1/bracket (3/10) := by
    unfold bracket
    rw [show (-7/10:ℝ) = -(7/10:ℝ) by ring, Real.rpow_neg q_pos.le]
    have h3 := q_power 3
    have h7 := q_power 7
    have h17 := q_power 17
    norm_num at h3 h7 h17
    rw [h7, h17, h3]
    norm_num [q, r]

  have witness_negative :
      qturanCoeff q (fun _ => 1) (-7/10) (7/10) (7/10) 2 < 0 := by
    let C : ℝ := bracket (-7/10)/(bracket (7/10)*bracket (17/10)) +
      1/bracket (7/10) + 1/bracket (3/10)
    have hC : (397/100:ℝ) < C := bracket_bound
    have hC0 : 0 ≤ C := by linarith
    have h3 : (4119/100000000000:ℝ) ≤ qprod q (r^3) := by
      simpa only [q, r] using qprod_numeric.1
    have h7 : (23803/100000000000:ℝ) ≤ qprod q (r^7) := by
      simpa only [q, r] using qprod_numeric.2.1
    have hq : qprod q q ≤ (63655/100000000000:ℝ) := by
      simpa only [q, r] using qprod_numeric.2.2
    have hqpos : 0 < qprod q q := qprod_pos q_pos.le q_lt q_pos.le q_lt
    have hprod0 : 0 ≤ qprod q (r^3) := le_trans (by norm_num) h3
    have hprod := mul_le_mul h3 h7 (by norm_num) hprod0
    have hden0 : 0 < (qprod q q)^2*(1-q) := mul_pos (sq_pos_of_pos hqpos) (sub_pos.mpr q_lt)
    have hden : (qprod q q)^2*(1-q) ≤ (63655/100000000000:ℝ)^2*(1-q) :=
      mul_le_mul_of_nonneg_right ((sq_le_sq₀ hqpos.le (by norm_num)).2 hq)
        (sub_nonneg.mpr q_lt.le)
    have hgap : (63655/100000000000:ℝ)^2*(1-q) <
        ((4119/100000000000:ℝ)*(23803/100000000000))*(397/100) := by norm_num [q,r]
    have hmul : 1 < (rqgamma q (3/10)*rqgamma q (7/10))*C := by
      rw [rqgamma_product q_pos q_lt]
      have hp3 := q_power 3
      have hp7 := q_power 7
      norm_num at hp3 hp7
      rw [hp3, hp7, div_mul_eq_mul_div]
      apply (lt_div_iff₀ hden0).2
      norm_num only [one_mul]
      calc
        _ ≤ (63655/100000000000:ℝ)^2*(1-q) := hden
        _ < ((4119/100000000000:ℝ)*(23803/100000000000))*(397/100) := hgap
        _ < ((4119/100000000000:ℝ)*(23803/100000000000))*C :=
          mul_lt_mul_of_pos_left hC (by norm_num)
        _ ≤ (qprod q (r^3)*qprod q (r^7))*C := mul_le_mul_of_nonneg_right hprod hC0
    rw [witness_formula]
    change 1-(rqgamma q (3/10)*rqgamma q (7/10))*C < 0
    linarith
  intro hclaim
  have h := hclaim q q_pos q_lt (fun _ => 1) admissible_one
    (-7/10) (7/10) (7/10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 2
  exact (not_lt_of_ge h.le) witness_negative

end D5.S3.Analytic.QGammaTuran.Result
