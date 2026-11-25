/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Certificate
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: The assembled labelled table and its group-prefix certificates. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table00
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table01
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table02
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table03
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table04
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table05
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table06
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table07
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Table08
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Tail0
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Tail1
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Tail2
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Data.Tail3

/-! Assembled inputs for checks inside the main smooth-predecessor theorem proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- The complete sequence of labelled candidate entries. -/
def table : List Nat :=
  table00 ++ table01 ++ table02 ++ table03 ++ table04 ++ table05 ++
    table06 ++ table07 ++ table08

/-- The exact terminal group states of the complete table. -/
def finalState : List (Nat × Nat) :=
  [(158, 666788788518726084220414761148564130847423878984056345975124),
    (137, 801233913950958545268731570369035512776519292842519690553078),
    (169, 857904198641485299538606350604906558674916929988295466678018),
    (137, 909949306243257161089748576216165910223948301160315894527376),
    (435, 924341172621050734553663018832260564730534690281768578475997),
    (1073, 945362421815433647492439708741201571103446045283131959774164),
    (1442, 956842510524588475480459479788969757542072248630720270812617),
    (431, 958502787791507354801884563661443450445411960147594917180573),
    (313, 967751286210557548512670796985822856929223054613958324474680),
    (917, 977131744990555781125762656621625086786466746287058688778952),
    (709, 980016327523196605362371598042113329483493602324873262069133),
    (359, 979128452128364683275289206031128421155328135998871710520389),
    (487, 981009262148971038656103024295653102092642246798082857845172),
    (510, 983454583165333275026659389115683112267477000124554976063822),
    (282, 985391320705153863795705918212057496587264333481353947234312),
    (452, 990490148463812900983366303994048786030481105529986507176199),
    (461, 988631602849539471918161662682207202108903765016805436338465),
    (323, 990428449938417041115543243178364145869387480108970206948234),
    (307, 991425802379303906217414801234548179791529968727827206985090),
    (274, 992008514498919069242750438548292604579854977929222293577981),
    (257, 992744674734130563426721359860948198583634418752532188265559),
    (124, 992402790657835900030982738827170100614033054167069919574333),
    (102, 993250441299316083741407951582762929893745394582089083983637),
    (160, 994572653762800062149314476874677416995922825130797995404114)]

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
