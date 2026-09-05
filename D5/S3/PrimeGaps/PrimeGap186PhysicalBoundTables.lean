/- GID: D5/S3/PrimeGaps/PrimeGap186PhysicalBoundTables
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the six exact integer bound tables and certify their lengths and aggregate rounded budgets. -/

import Mathlib

/-!
Exact integer tables from `openai/PrimeGaps186` commit
`61340d0b74163003b32756bb16e91d9209a5e330`. The rows themselves are data, not assumptions.
Theorems in this file certify their table lengths and the exact sums of the rounded budget columns.
-/

namespace D5.S3.PrimeGaps.PrimeGap186PhysicalBoundTables

abbrev OuterBoundRow := ℕ × ℕ × ℕ × ℕ
abbrev InnerBoundRow := ℕ × ℕ

def outerOrderTwoBounds : List OuterBoundRow :=
  [(961904, 11, 10, 1), (502424, 2285, 577, 1),
   (483341, 11432060, 2670744, 12), (547373, 3056104728, 915663654, 3346),
   (563915, 37877639997, 12045112668, 42720),
   (583181, 300901046806, 102336788484, 350961),
   (604629, 2682803914309, 980771899210, 3244207),
   (620671, 3338737765461, 1286194297547, 4144522),
   (629321, 7260461043003, 2875471614189, 9138326),
   (635211, 1211995036896, 489032601185, 1539747),
   (616326, 8286469691008, 3147682021553, 10214338),
   (593862, 4616001082128, 1627937050440, 5482540),
   (573977, 2353287968619, 775291485464, 2701470),
   (553178, 1146587714775, 350863740368, 1268537),
   (531463, 529511465762, 149562603056, 562833),
   (508862, 229315416929, 59379253693, 233381),
   (459016, 631278927, 133008010, 580)]

def outerOrderFiveHalvesBounds : List OuterBoundRow :=
  [(7266522, 27, 1426, 1), (1241454497, 1, 821, 1),
   (1208324400, 1, 1392, 1), (1152630107, 1, 1765, 1),
   (1126190783, 1, 3334, 1), (1096246679, 1, 5753, 1),
   (1058983690, 1, 10303, 1), (967816560, 1, 18815, 1),
   (867471653, 1, 2089, 1), (603785822, 1, 11427, 1),
   (32188902, 16, 16011, 1), (1308239, 14362, 24579, 1),
   (386321, 7065761, 1054524, 6), (373849, 17914115, 2503735, 14),
   (377891, 260216687, 37159538, 197), (385136, 3305952377, 490372043, 2547),
   (395013, 38054077523, 5937779759, 30064),
   (405835, 352112119115, 57993623042, 285799),
   (419505, 3006707964277, 529135146833, 2522662),
   (432001, 19352692647427, 3611707956032, 16720799),
   (445139, 14498518468563, 2872865686933, 12907719),
   (457321, 28197429960534, 5897287451435, 25790569),
   (525975, 57148020076132, 15810035599715, 60116961),
   (518733, 69886316496332, 18805329967080, 72504766),
   (515168, 69366993102523, 18409874222209, 71471327),
   (512357, 62684551010344, 16455348517458, 64233828),
   (509770, 53862830801099, 13997130877252, 54915393),
   (507320, 44981355032435, 11577030541299, 45639918),
   (504951, 36911787941323, 9411611503675, 37277308),
   (502604, 29975466544992, 7572139370727, 30131606),
   (503256, 50573740961589, 12808689167903, 50903176),
   (498048, 32438336646873, 8046407139897, 32311736),
   (492222, 20308616081603, 4920425453752, 19992702),
   (485810, 12358345921158, 2916712121993, 12007621),
   (433769, 15056954296612, 2833062492447, 13062511)]

def innerBaseOrderTwoBounds : List InnerBoundRow :=
  [(25777, 1), (1511410893, 14), (18120016651, 161),
   (903601038105, 8027), (425243194887, 3778),
   (4871216699917, 43272), (23946432, 1)]

def innerBaseOrderFiveHalvesBounds : List InnerBoundRow :=
  [(1, 1), (3229104, 1), (29825526, 1), (77797373079, 692),
   (131978724894, 1173), (29268478373079, 2600),
   (5548294545493, 49286), (30283518217418, 269010),
   (12009121688668, 106678), (686922192553, 6102)]

def innerEnlargedOrderTwoBounds : List InnerBoundRow :=
  [(467789, 1), (381747797, 383), (386210860, 387),
   (99885644276, 99970), (247732013063, 247941),
   (381057139991, 381379), (266162792752, 266388),
   (337097314828, 337382), (34427294106, 34457),
   (36820947233, 36852), (18106118, 19)]

def innerEnlargedOrderFiveHalvesBounds : List InnerBoundRow :=
  [(2, 1), (107126908277, 107218), (1, 1), (61, 1), (137, 1),
   (177471603, 178), (327802576, 329), (50667881720, 50711),
   (143104919759, 143226), (1323952422879, 1325069),
   (697854132745, 698443), (4234127556194, 4237698),
   (11632061739670, 11641870), (3641610451935, 3644681),
   (6136054632765, 6141229), (3690866567521, 3693979),
   (737132501820, 737755)]

set_option maxRecDepth 4096 in
theorem bound_table_lengths :
    outerOrderTwoBounds.length = 17 ∧
    outerOrderFiveHalvesBounds.length = 35 ∧
    innerBaseOrderTwoBounds.length = 7 ∧
    innerBaseOrderFiveHalvesBounds.length = 10 ∧
    innerEnlargedOrderTwoBounds.length = 11 ∧
    innerEnlargedOrderFiveHalvesBounds.length = 17 := by
  decide

/-- Rounded budget-column sums, in units of `10^-12`, for the six exact tables. -/
set_option maxRecDepth 4096 in
theorem rounded_budget_sums :
    (outerOrderTwoBounds.map (fun r => r.2.2.2)).sum = 38927522 ∧
    (outerOrderFiveHalvesBounds.map (fun r => r.2.2.2)).sum = 622829241 ∧
    (innerBaseOrderTwoBounds.map (fun r => r.2)).sum = 55254 ∧
    (innerBaseOrderFiveHalvesBounds.map (fun r => r.2)).sum = 435544 ∧
    (innerEnlargedOrderTwoBounds.map (fun r => r.2)).sum = 1405159 ∧
    (innerEnlargedOrderFiveHalvesBounds.map (fun r => r.2)).sum = 32422390 := by
  decide

/-- Total rounded budget mass across all six source tables. -/
set_option maxRecDepth 4096 in
theorem total_rounded_budget_sum :
    (outerOrderTwoBounds.map (fun r => r.2.2.2)).sum +
    (outerOrderFiveHalvesBounds.map (fun r => r.2.2.2)).sum +
    (innerBaseOrderTwoBounds.map (fun r => r.2)).sum +
    (innerBaseOrderFiveHalvesBounds.map (fun r => r.2)).sum +
    (innerEnlargedOrderTwoBounds.map (fun r => r.2)).sum +
    (innerEnlargedOrderFiveHalvesBounds.map (fun r => r.2)).sum = 696075110 := by
  decide

#print axioms outerOrderTwoBounds
#print axioms outerOrderFiveHalvesBounds
#print axioms innerBaseOrderTwoBounds
#print axioms innerBaseOrderFiveHalvesBounds
#print axioms innerEnlargedOrderTwoBounds
#print axioms innerEnlargedOrderFiveHalvesBounds
#print axioms bound_table_lengths
#print axioms rounded_budget_sums
#print axioms total_rounded_budget_sum

end D5.S3.PrimeGaps.PrimeGap186PhysicalBoundTables
