/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233128SquareStrip.finite_certificate
   digest: Hardin's order-fourteen recurrence for literal seven-column square strips. -/

/-
admission_basis: open-problem-resolution (#28672; Proved)
escape_witness: none; all-height class reduction is semiconjugacy iteration.
After normalizing finite one-step premises, v_eq_w is an instance of
Function.Semiconj.iterate_right. It and its downstream chain are bind-only.
Declaration namespace: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
Direct frozen dependencies (declaration GIDs and statement_ids):
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish_fst
statement_id: sha256:5859cc0f84f4e6a91313521f32ea6d187c4822bb52d4e438939da5e000940bd5
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish_snd
statement_id: sha256:1ada14ea452d6f35f959dbbd5a034265c8c6921cd041422cad27ec166a94d24c
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good_iff
statement_id: sha256:59d0ffb034f7f2361718e6d2566eb24417785b9a178f6fcb44f336c1199d3d62
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthInstDecidableLegal
statement_id: sha256:6c1f0ba304e14673a1966eca92d67e12ccf8925c940c5ba2391b4b478ac39547
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthLegal
statement_id: sha256:989eff70ea57c1a27e750e36536ea11ddb8f9aa5a27d74dce459fc2432ec52e8
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthNormal._proof_1
statement_id: sha256:3ea64915f32c9d14cb1f8694caa8b29adcc02a50f28a6142292cccc5f150cf1a
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthStep
statement_id: sha256:bd12c5c5928f8822063ec100e0e6e92c5300f5907da4aa64e85595a1ee4c7cb5
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthStep.eq_1
statement_id: sha256:f0e1fc897c2470d95f639750def23fe05e87fb9061f66dd0ca788b6eda04aec4
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthTotal
statement_id: sha256:c4c082551693765b0f6c344f5f6ff825120f019a96ec4d79015c10c10bf774d0
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthTotal.eq_1
statement_id: sha256:98c91caccabbd60e8a6fae4d99818e8a614dfba06487712acc8167120f8e9727
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthV
statement_id: sha256:4f3953ec5d8902b74486197a6f4d782f3fb58c6627a5740a5242632a7560f9ed
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.widthV.eq_2
statement_id: sha256:02a910fcd311188b871be135dbe86f61c98a47ead76d48f62a22196f30991d60
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.width_counting_bridge
statement_id: sha256:a6ad861eda2ca48bc91989542e4b7cc27d81aec8df9a91b8db40c9398c577c72
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowFinish
statement_id: sha256:ded50bd8c5de69b5b2324e575fee135f275ae05b5bb30b328b0e5c0313d86b07
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.rowWeight
statement_id: sha256:076a03b0e19556ba67d0faed8d8d552fb3d55e6c40992d9c52c88faad85e373a
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255LiteralBridge.scanner_fibres
statement_id: sha256:63a356389be3d9bf756c53fb12271299a7668c1123562d84a2e34e78a341fc90
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.PairRow
statement_id: sha256:e97b1a06b78d944d101465bdc94301416cfe964a1e9cbf900093e9cd04d04132
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.Row
statement_id: sha256:bfdef18389c25a4e0e0289ec0c41644aaf42d71c7a4d540ac5103952779dfd2c
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowLegal
statement_id: sha256:566fa77bfdf47796ff0524d5a78f68b96413ca55006aa1429a767aad72408b70
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.decidableRowProper
statement_id: sha256:3008fde3ace25a7a7b6733df6dfc91bda36cb584aea7e431b1c29d583dc1893d
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.first_fibres
statement_id: sha256:3a96f3fdc23bad6d14d0e164907d2eff591563f9c6fb4212e2552316abd3de04
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowLegal
statement_id: sha256:ad59d456a8f5b2710481be3ed4a9d79e276a0e4319f7b6918310d350fc440508
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255PairTransfer.rowProper
statement_id: sha256:be16a774dbabce7949eb6e2bfc0026252c129abfda8a7377875535297a177b53
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233255ShapeSymmetry.full_row
statement_id: sha256:f81e65c6e42bf750ca73737a7ace4b7b696a7b7a57684908ba1ce134acfcf88c
GID: D5/S3/Observer/Separation/BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.WidthRow
statement_id: sha256:63d18919d9321000a9a3541c82cd4a7aa88a0da2c26ce61e51d7cede756ff789
bonds_iff: proof_shape=bind-only; consumers=counting_bridge
v: proof_shape=bind-only; consumers=counting_bridge, v_eq_w
total: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
valid_next: proof_shape=bind-only; consumers=initial_valid, v_eq_w
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_fibres: proof_shape=bind-only; consumers=initial_counts
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, shifted_count
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=shifted_count
distribution: proof_shape=bind-only; consumers=distribution_step
distribution_step: proof_shape=bind-only; consumers=shifted_count
shifted_count: proof_shape=bind-only; consumers=result
distribution_relation: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result (#28672)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Certificate
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Lean.Elab.Tactic.Omega

/-! Hardin's order-fourteen recurrence for literal seven-column square strips. -/

set_option Elab.async false
set_option maxRecDepth 100000

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip

open HardinA233175PairStrip (Seen good finish)
open HardinA233251TriangleStrip (widthLegal colour_bond_iff)
open HardinA233255PairTransfer (Row rowLegal PairRow rowProper)
open HardinA233255LiteralBridge (rowFinish rowWeight scanner_fibres)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

attribute [local instance 2000] HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local instance 2000] Pi.instFintype
open HardinA233251TriangleStrip (widthV widthStep widthTotal width_counting_bridge)
open private row_counts from
  D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128Certificate

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (labels c) d := by
  simp only [bonds, colour_bond_iff, compatible, labels]

private abbrev v := widthV rowLegal labels compatible
private abbrev total := widthTotal rowLegal labels

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) :=
  width_counting_bridge rowLegal labels compatible bonds bonds_iff n

private theorem valid_next (s : Seen) (c : Row)
    (hs : s.1 = true ∨ ∃ i, c i = 1) (hc : rowLegal c ∧ good s c) :
    Valid (finish s c) (labels c) := by
  refine ⟨HardinA233175PairStrip.finish_fst s c |>.mpr hs, ?_, ?_⟩
  · intro j
    exact (colour_bond_iff _ _).mp (hc.1 j)
  · intro ht j
    have htwo : ∀ i, c i ≠ 2 := by
      intro i hi
      have hh := (HardinA233175PairStrip.finish_snd s c).mpr (Or.inr ⟨i, hi⟩)
      simp [ht] at hh
    have hstate : s.2 ≠ true := by
      intro hi
      have hh := (HardinA233175PairStrip.finish_snd s c).mpr (Or.inl hi)
      simp [ht] at hh
    have hthree : ∀ i, c i ≠ 3 := by
      intro i hi
      rcases ((HardinA233175PairStrip.good_iff s c).mp hc.2 i).2 hi with
        hh | ⟨r, _, hr⟩
      · exact hstate hh
      · exact htwo r hr
    have hb : ∀ x : Fin 6, beta x = 2 ↔ x = 2 ∨ x = 3 := by decide +kernel
    intro hx
    rcases (hb _).mp hx with hh | hh
    · exact htwo _ hh
    · exact hthree _ hh

private theorem initial_valid (c : Row)
    (hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c) :
    Valid (finish (false, false) c) (labels c) := by
  have hedge : (0 : Fin 6) ≠ c 1 ∧ (c 1).val ≠ 5 := by
    have hh := hc.2.1 (0 : Fin 6)
    change c 0 ≠ c 1 ∧ (c 0).val + (c 1).val ≠ 5 at hh
    simpa only [hc.1, Fin.val_zero, zero_add] using hh
  have hcol : ∀ x : Fin 6, x ≠ 0 → x.val ≠ 5 → x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    decide +kernel
  have hone : ∃ i, c i = 1 := by
    rcases hcol _ (Ne.symm hedge.1) hedge.2 with hi | hi
    · exact ⟨1, hi⟩
    · rcases ((HardinA233175PairStrip.good_iff _ c).mp hc.2.2 1).1 hi with
        hh | ⟨i, _, hi⟩
      · cases hh
      · exact ⟨i, hi⟩
  exact valid_next _ c (Or.inr hone) ⟨hc.2.1, hc.2.2⟩

private theorem initial_fibres (k : Fin 21) :
    firstCount k = ∑ q : Fin 6 → Fin 3, rowWeight (false, false) q *
      if rowProper (Fin.cons 0 q) ∧
        boundaryClass (rowFinish (false, false) q) (Fin.cons 0 q) = k then 1 else 0 := by
  have hh := HardinA233255PairTransfer.first_fibres (fun t q =>
    if rowProper q ∧ boundaryClass t q = k then (1 : ℤ) else 0)
  unfold firstCount
  convert hh using 1
  apply Finset.sum_congr rfl
  intro c _
  have hr : rowProper (fun j => beta (c j)) ↔ rowLegal c := by
    simp only [rowProper, rowLegal, colour_bond_iff]
  change (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
      boundaryClass (finish (false, false) c) (labels c) = k then (1 : ℤ) else 0) =
    if c 0 = 0 ∧ good (false, false) c then
      (if rowProper (fun j => beta (c j)) ∧
        boundaryClass (finish (false, false) c) (labels c) = k then 1 else 0) else 0
  simp only [hr]
  by_cases hg : good (false, false) c <;> by_cases hz : c 0 = 0 <;> simp [hg, hz]

private theorem initial_counts : ∀ k, firstCount k =
    ![32, 0, 32, 32, 32, 16, 32, 32, 32, 32, 16, 32, 32, 16, 32, 16, 32, 16, 32, 16, 16] k := by
  simp only [initial_fibres]
  simp_rw [← (Fin.consEquiv (fun _ : Fin 6 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 5 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 4 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 3 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 2 => Fin 3)).sum_comp,
    Fintype.sum_prod_type,
    ← (Fin.consEquiv (fun _ : Fin 1 => Fin 3)).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv]
  decide +kernel

/-- The exact single-row transitions and first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k =
      ![32, 0, 32, 32, 32, 16, 32, 32, 32, 32, 16, 32, 32, 16, 32, 16, 32, 16, 32, 16, 16] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 21 → ℤ
  | 0, _ => 1
  | n + 1, i => ∑ k : Fin 21, transfer i k * w n k

private theorem v_eq_w (n : ℕ) (s : Seen) (p : PairRow) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, widthV, widthStep]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (labels c) else 0) =
        ∑ k : Fin 21, (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (labels c) = k then (1 : ℤ) else 0) * w n k := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s c (Or.inl h.1) ⟨hc.1, hc.2.2⟩)]
        simp [hc]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    change (∑ k : Fin 21, classCount s p k * w n k) = _
    simp_rw [finite_certificate.1 s p h]
    rfl

private theorem a_eq_w (n : ℕ) :
    (a (n + 1) : ℤ) = ∑ k : Fin 21,
    ![32, 0, 32, 32, 32, 16, 32, 32, 32, 32, 16, 32, 32, 16,
      32, 16, 32, 16, 32, 16, 16] k * w n k := by
  rw [counting_bridge, total, widthTotal]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (labels c) else 0) =
      ∑ k : Fin 21, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (labels c) = k then (1 : ℤ) else 0) *
          w n k := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      simp [hc]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  change (∑ k : Fin 21, firstCount k * w n k) = _
  simp_rw [finite_certificate.2]

private def distribution (r : Fin 15) (k : Fin 21) : ℤ :=
  ![![32, 0, 32, 32, 32, 16, 32, 32, 32, 32, 16, 32, 32, 16, 32, 16, 32, 16, 32, 16, 16]
    , ![4096, 67584, 118784, 126976, 94208, 61440, 110592, 102400, 69632, 106496, 59392, 90112,
      94208, 40960, 53248, 51200, 77824, 49152, 65536, 34816, 16384]
    , ![524288, 241172480, 395313152, 432013312, 288882688, 200278016, 374341632, 308805632,
      177733632, 335020032, 204210176, 287834112, 304611328, 111673344, 120061952, 170131456,
      211812352, 166723584, 185597952, 106430464, 29884416]
    , ![67108864, 798931025920, 1286141378560, 1420157779968, 911069937664, 643305570304,
      1233729355776, 958784339968, 510832672768, 1061393793024, 675786260480, 931135488000,
      988379348992, 331249352704, 325209554944, 559822143488, 627602096128, 548682072064,
      569552928768, 345845530624, 72880226304]
    , ![8589934592, 2602075871510528, 4158395925921792, 4613026804137984, 2909548285263872,
      2067846364397568, 4014170924122112, 3037332152254464, 1562861289603072,
      3391984781754368, 2201415552335872, 3008401252548608, 3196718388609024,
      1028541588176896, 967879470088192, 1822298789117952, 1945852113321984,
      1782608996335616, 1800321441464320, 1123876977246208, 206003811385344]
    , ![1099511627776, 8421583968624705536, 13417043525611028480, 14913891167874580480,
      9340471124724547584, 6655273514183950336, 12988110845476077568, 9715358410307796992,
      4923410759041417216, 10890031553446936576, 7125628645627920384, 9706186284308889600,
      10318336084538294272, 3261773811564937216, 3011755862524952576, 5898375756936904704,
      6164789073614471168, 5762986842894893056, 5756210552732909568, 3637214151496957952,
      625740863460343808]
    , ![140737488355328, 27186556315061744304128, 43256275172697244172288,
      48123481923182751907840, 30050691570519630675968, 21433946099959847714816,
      41924116032420585668608, 31207932590119079378944, 15711943473825467858944,
      35035720790768963551232, 23004035193625093603328, 31293380371011598286848,
      33273417783532568182784, 10439398683127779950592, 9560162335251121569792,
      19042888230396862922752, 19720675189241518489600, 18594963307683337207808,
      18488801079567239348224, 11743132580300103614464, 1964983990028995657728]
    , ![18014398509481984, 87670189656589582253162496, 139414194613968215100882944,
      155157779742642140698640384, 96768397445434894377287680, 69050751137036833155710976,
      135190298571474140718432256, 100428168707494462382669824, 50421106839231713937195008,
      112819812886054825759866880, 74184016241067774011506688, 100859923309378926442184704,
      107250647031214474744823808, 33542607885089779310657536, 30609617370774502601916416,
      61411770732299305898475520, 63349344050710970695155712, 59951660867844537782894592,
      59496691975292032745734144, 37871825117476739367305216, 6262111869232140701925376]
    , ![2305843009213693952, 282589476774080430473752870912, 449272538371078074673934630912,
      500084633776869700757559967744, 311729211594084581451497472000,
      222479879552376539603424772096, 435755733155309210549090254848,
      323427997412713422579249971200, 162189765476928180983502471168,
      363434980416688102276081909760, 239121141817963103455629279232,
      325031633403419985760695091200, 345638811722645049583601713152,
      107953508072835785800269430784, 98367009845136503342230405120,
      197954470875328800446664933376, 203862581409331296559664463872,
      193226228600644981227587108864, 191608016534644479923673104384,
      122077870713517305584588685312, 20083749375895227985679089664]
    , ![295147905179352825856, 910706968049504819596028037562368,
      1447737787581112579480453214371840, 1611579943598610307548243866681344,
      1004363039135820225184310398812160, 716864196267741155319160135221248,
      1404310460594318976016965418614784, 1041932149927972401511709299179520,
      522239376395171496803510513565696, 1170951037575728154187240002551808,
      770623342814940376372628317798400, 1047387825967764770690040537808896,
      1113809775202295403166229160001536, 347680003114843249799372843515904,
      316605496852930698101174346711040, 637958175027478617994187604230144,
      656540147644683788010893508345856, 622690361857789257688683223449600,
      617270165799439661631536095035392, 393429615498564208009721459769344,
      64587117501847863917664706494464]
    , ![37778931862957161709568, 2934722929016439975716244209199480832,
      4665093902242044711012031375716909056, 5193190677458974745023384893383507968,
      3236183081052536136119356243908231168, 2309899605412633078049304091601928192,
      4525332267979746565697555547688009728, 3357068033533170771451807555334963200,
      1682284314606773528947719867931295744, 3772945779734363283187796703893782528,
      2483311735316096250618185674408329216, 3375039081139117032831879823530917888,
      3589096349276089707323051679441485824, 1120083345710379345375179888373268480,
      1019702550055788202736793853383147520, 2055807560491060143269612965419024384,
      2115065134360052489411195908067950592, 2006566567211994696582717245992468480,
      1988822196553884274196646203691630592, 1267823222679993490966041860159569920,
      207943584754749658976116196046274560]
    , ![4835703278458516698824704, 9456733307736285249083662469049530449920,
      15032349244403362357231640729022067900416, 16734231236815824943855486073745675649024,
      10427680370378168595745002311829365456896, 7443095044465421360374418125254832422912,
      14582233433558026079324120243674617479168, 10816970521473624605888214649764782800896,
      5420091071001064078872533112339254214656, 12157239233331844888471615448961238695936,
      8002128931732707539405712344698654294016, 10875409451045017479222579734153321775104,
      11565199099078706202571866548300360450048, 3608899175430706154130958423780164108288,
      3285104575987869327179060734440400486400, 6624563415708538266818697968641655177216,
      6814667895269837464297440940568457773056, 6465835444965247877170661668528200876032,
      6408279712620633775932591388755782270976, 4085395497426425689880823352265038364672,
      669816213572110532998136578748792700928]
    , ![618970019642690137449562112, 30472571852702835826316267803913063080394752,
      48438606044037927239829384676449147189985280,
      53922828475291039101167918498640707616505856,
      33600636469705505325551931874862456180310016,
      23983679625428578374233528523697066659020800,
      46988525829313674579910883713339573628043264,
      34854719798417606963431410972629515064311808,
      17464107273879213852538558445421363114016768,
      39173705939661354412998244892224709489328128,
      25785385303591760141364696494521117921247232,
      35043747458297126954853121897651646683414528,
      37266494210955410676267780968719519896829952,
      11628449544552830232457693191202002689851392,
      10584631331368360487446111246528730659553280,
      21346444777706099443508561398751938861858816,
      21957874503231385706559281127599043707404288,
      20834897480904332687564619459464992114343936,
      20648923291268449115477737814994577503813632,
      13164447994051425526985344642129585810440192,
      2158015484083582967852199416940249328123904]
    , ![79228162514264337593543950336, 98191641920223201419925228010544108518066094080,
      156083036622390851774357419449432911496309899264,
      173755126378880953125013157769828374422321364992,
      108270333088928681950573602808265450005360279552,
      77282082730597898538566806869520076859053703168,
      151410903437499538254791988104860770380164366336,
      112310909828967249446549892270865796674680258560,
      56272983244642904840996677817553899853495402496,
      126228257381698531352107573780841133209821380608,
      83088149210117680747536604883834831477783134208,
      112920988848732663948740019318397250743413243904,
      120083373657867778002566161878491027833899450368,
      37469545009009150221613358364675152462307393536,
      34105442957395458918222479828047714290587664384,
      68784582151151915964871595329883521125342773248,
      70753232957742638571108659046966628685185024000,
      67136122455063337091554259623246847448302223360,
      66536164431368774763722825062656834562569535488,
      42419770068087648323567948745087851739914174464,
      6953298441810704125727788755638993425564434432]
    , ![10141204801825835211973625643008, 316401736269613633069631066804359659490993401495552,
      502943819625933413510714787162326862210627847323648,
      559888790720286709471449818775119139846656842792960,
      348877015278574999158599358713683623401428573224960,
      249024535549373322322793801871366505419890097127424,
      487889478223201356057192415352293762068524470108160,
      361896304816009810992953735502586292519396534386688,
      181325664506636085498376888850391552559707840315392,
      406742407278879919209308696681700275662940981428224,
      267733947291945429998205532265014004073937690951680,
      363863479794505691569570530978261660758245975785472,
      386942795929221567983040922532077545672743776681984,
      120736628985025442741003231615086997051204498882560,
      109895694452423732452673830576184538390694266404864,
      221643753837737212283436655827261342547458945712128,
      227985200403717303581700110436762577695305384329216,
      216331802358199171673796107196982762711122333138944,
      214397622742722775495698019362722383956580782571520,
      136688742817401150062654868725000965292226632482816,
      22404896773555508554468274458092317399090810847232]] r k

private theorem distribution_step : ∀ (r : Fin 14) (k : Fin 21),
    distribution r.succ k = ∑ i : Fin 21, distribution r.castSucc i * transfer i k := by
  decide +kernel

private theorem shifted_count (r : Fin 15) (n : ℕ) :
    (a (n + r.val + 1) : ℤ) = ∑ k : Fin 21, distribution r k * w n k := by
  induction r using Fin.induction generalizing n with
  | zero => exact a_eq_w n
  | succ r ih =>
    rw [show n + r.succ.val + 1 = (n + 1) + r.castSucc.val + 1 by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega, ih]
    simp only [w, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, ← distribution_step]

private theorem distribution_relation : ∀ k : Fin 21,
    distribution 14 k =
      7168 * distribution 13 k
      - 19070976 * distribution 12 k
      + 26086473728 * distribution 11 k
      - 21081846972416 * distribution 10 k
      + 10809917287956480 * distribution 9 k
      - 3649692508960587776 * distribution 8 k
      + 824336623994081902592 * distribution 7 k
      - 124561639357723747287040 * distribution 6 k
      + 12414326720213201465638912 * distribution 5 k
      - 792885332473813431379558400 * distribution 4 k
      + 31062140009178282014900486144 * distribution 3 k
      - 704387882353381376417601683456 * distribution 2 k
      + 8398185226512019784915658735616 * distribution 1 k
      - 40564819207303340847894502572032 * distribution 0 k := by
  decide +kernel

/-- Hardin's recurrence for every height at least fifteen, with every shift explicit. -/
theorem result (n : ℕ) :
    (a (n + 15) : ℤ) =
      7168 * a (n + 14)
      - 19070976 * a (n + 13)
      + 26086473728 * a (n + 12)
      - 21081846972416 * a (n + 11)
      + 10809917287956480 * a (n + 10)
      - 3649692508960587776 * a (n + 9)
      + 824336623994081902592 * a (n + 8)
      - 124561639357723747287040 * a (n + 7)
      + 12414326720213201465638912 * a (n + 6)
      - 792885332473813431379558400 * a (n + 5)
      + 31062140009178282014900486144 * a (n + 4)
      - 704387882353381376417601683456 * a (n + 3)
      + 8398185226512019784915658735616 * a (n + 2)
      - 40564819207303340847894502572032 * a (n + 1) := by
  have h0 := shifted_count (0 : Fin 15) n
  have h1 := shifted_count (1 : Fin 15) n
  have h2 := shifted_count (2 : Fin 15) n
  have h3 := shifted_count (3 : Fin 15) n
  have h4 := shifted_count (4 : Fin 15) n
  have h5 := shifted_count (5 : Fin 15) n
  have h6 := shifted_count (6 : Fin 15) n
  have h7 := shifted_count (7 : Fin 15) n
  have h8 := shifted_count (8 : Fin 15) n
  have h9 := shifted_count (9 : Fin 15) n
  have h10 := shifted_count (10 : Fin 15) n
  have h11 := shifted_count (11 : Fin 15) n
  have h12 := shifted_count (12 : Fin 15) n
  have h13 := shifted_count (13 : Fin 15) n
  have h14 := shifted_count (14 : Fin 15) n
  change (a (n + 1) : ℤ) = _ at h0
  change (a (n + 2) : ℤ) = _ at h1
  change (a (n + 3) : ℤ) = _ at h2
  change (a (n + 4) : ℤ) = _ at h3
  change (a (n + 5) : ℤ) = _ at h4
  change (a (n + 6) : ℤ) = _ at h5
  change (a (n + 7) : ℤ) = _ at h6
  change (a (n + 8) : ℤ) = _ at h7
  change (a (n + 9) : ℤ) = _ at h8
  change (a (n + 10) : ℤ) = _ at h9
  change (a (n + 11) : ℤ) = _ at h10
  change (a (n + 12) : ℤ) = _ at h11
  change (a (n + 13) : ℤ) = _ at h12
  change (a (n + 14) : ℤ) = _ at h13
  change (a (n + 15) : ℤ) = _ at h14
  rw [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0]
  simp_rw [distribution_relation, sub_mul, add_mul]
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, Finset.mul_sum]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233128SquareStrip
