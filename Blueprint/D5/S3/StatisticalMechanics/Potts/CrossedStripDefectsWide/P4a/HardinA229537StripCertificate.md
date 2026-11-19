# HardinA229537StripCertificate

## Abstract

Four-row exact-defect HDA strips.

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.1 (zero_counts).**

$$\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(14\right)), (\sum_{(r: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, p, r\right) = 0) \land (\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left((r\left(0\right), (r\left(1\right), (r\left(2\right), r\left(3\right))))\right) = j)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA233177PairTransfer}.\operatorname{Q}\left(\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left((p\left(0\right), (p\left(1\right), (p\left(2\right), p\left(3\right))))\right), j\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.zero_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.2 (one_counts).**

$$\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(14\right)), (\sum_{(r: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, p, r\right) = 1) \land (\operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left((r\left(0\right), (r\left(1\right), (r\left(2\right), r\left(3\right))))\right) = j)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229537StripData}.\operatorname{T}\left(\operatorname{Fin}.\operatorname{castAdd}\left(14, \operatorname{HardinA233177PairTransfer}.\operatorname{cls}\left((p\left(0\right), (p\left(1\right), (p\left(2\right), p\left(3\right))))\right)\right), \operatorname{Fin}.\operatorname{natAdd}\left(14, j\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.one_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.3 (cost_relabel).**

$$\forall (e: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(3\right)\right)), (\forall (p: \operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\forall (r: \operatorname{HardinA233177PairTransfer}.\operatorname{Col}), (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, \operatorname{HardinA233177PairTransfer}.\operatorname{column}\left((\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(p\right)\right), \operatorname{HardinA233177PairTransfer}.\operatorname{column}\left((\operatorname{HardinA233177PairTransfer}.\operatorname{relabel}\left(e\right): \operatorname{HardinA233177PairTransfer}.\operatorname{Col} \to \operatorname{HardinA233177PairTransfer}.\operatorname{Col})\left(r\right)\right)\right) = \operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, \operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(p\right), \operatorname{HardinA233177PairTransfer}.\operatorname{column}\left(r\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.cost_relabel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Definition 1.4 (Z).**

$$\operatorname{HardinA229537StripCertificate}.\operatorname{Z} = \operatorname{Fin}.\operatorname{append}\left(\operatorname{HardinA233177PairTransfer}.\operatorname{W}, (\begin{pmatrix}2340880&783812&557050&719483&0&557050&417502&0&417502&783812&127826&0&0&0\\13154182&4401225&3124692&4036330&0&3124692&2340880&0&2340880&4401225&719483&0&0&0\\73848212&24716429&17555407&22676115&0&17555407&13154182&0&13154182&24716429&4036330&0&0&0\\414752726&138796163&98564641&127317400&0&98564641&73848212&0&73848212&138796163&22676115&0&0&0\\2328976316&779430930&553548889&715021167&0&553548889&414752726&0&414752726&779430930&127317400&0&0&0\\13078925146&4376977302&3108407246&4015155576&0&3108407246&2328976316&0&2328976316&4376977302&715021167&0&0&0\\73445604900&24579465270&17455902448&22547900917&0&17455902448&13078925146&0&13078925146&24579465270&4015155576&0&0&0\\412444183090&138028873535&98025070170&126619691016&0&98025070170&73445604900&0&73445604900&138028873535&22547900917&0&0&0\\2316125942632&775117817811&550473056625&711049831077&0&550473056625&412444183090&0&412444183090&775117817811&126619691016&0&0&0\\13006491777522&4352766648145&3091243760443&3992981269270&0&3091243760443&2316125942632&0&2316125942632&4352766648145&711049831077&0&0&0\\73039491498464&24443483455380&17359258425667&22423074904889&0&17359258425667&13006491777522&0&13006491777522&24443483455380&3992981269270&0&0&0\\410162067440982&137265308284400&97482974953844&125919439678494&0&97482974953844&73039491498464&0&73039491498464&137265308284400&22423074904889&0&0&0\\2303314113185784&770829790357720&547427375725382&707115758914671&0&547427375725382&410162067440982&0&410162067440982&770829790357720&125919439678494&0&0&0\\12934536678297246&4328687038183557&3074143903543504&3970893133579718&0&3074143903543504&2303314113185784&0&2303314113185784&4328687038183557&707115758914671&0&0&0\end{pmatrix}: \operatorname{Fin}\left(14\right) \to \left(\operatorname{Fin}\left(14\right) \to \operatorname{Int}\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.Z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.5 (zero_powers).**

$$\forall (i: \operatorname{Fin}\left(22\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{HardinA233177PairTransfer}.\operatorname{Q}, \operatorname{Fin}.\operatorname{val}\left(i\right)\right), (1: \operatorname{Fin}\left(14\right) \to \operatorname{Int})\right) = \operatorname{HardinA229537StripCertificate}.\operatorname{Z}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.zero_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Definition 1.6 (W).**

$$\forall (i: \operatorname{Fin}\left(22\right)), (\operatorname{HardinA229537StripCertificate}.\operatorname{W}\left(i\right) = \operatorname{Fin}.\operatorname{append}\left((\begin{pmatrix}0&0&0&0&0&0&0&0&0&0&0&0&0&0\\0&12&8&8&6&8&6&3&6&12&6&0&3&6\\120&49&31&42&9&31&20&8&20&49&20&0&8&9\\724&428&322&328&55&322&264&51&264&428&134&0&51&55\\6160&2704&1903&2150&288&1903&1468&263&1468&2704&794&0&263&288\\40920&18296&13321&14982&1652&13321&10470&1528&10470&18296&4878&0&1528&1652\\280152&117021&83683&96664&9184&83683&64826&8447&64826&117021&30046&0&8447&9184\\1815752&744816&535878&625464&51775&535878&415062&47749&415062&744816&181846&0&47749&51775\\11665456&4657599&3336391&3940754&290259&3336391&2571816&267374&2571816&4657599&1102432&0&267374&290259\\73475644&28863570&20687092&24636152&1631121&20687092&15914804&1503295&15914804&28863570&6622478&0&1503295&1631121\\458085456&177198520&126828621&152147306&9157038&126828621&97329928&8437555&97329928&177198520&39687986&0&8437555&9157038\\2825893800&1080173062&772848457&932633526&51428874&772848457&592061986&47392544&592061986&1080173062&236690978&0&47392544&51428874\\17297388672&6543135579&4678478409&5674694984&288789678&4678478409&3578207734&266113563&3578207734&6543135579&1407355134&0&266113563&288789678\\105143454200&39425416516&28178327908&34328155076&1621769497&28178327908&21522210170&1494452097&21522210170&39425416516&8340654622&0&1494452097&1621769497\\635447036928&236454026529&168927769187&206582067498&9107154045&168927769187&128868177900&8392132878&128868177900&236454026529&49298924172&0&8392132878&9107154045\\3821058103316&1412391957008&1008692705678&1237661620888&51142521763&1008692705678&768676702904&47127366187&768676702904&1412391957008&290652802934&0&47127366187&51142521763\\22876484910768&8406271468352&6001616749467&7385784342638&287196465468&6001616749467&4569223737796&264648564551&4569223737796&8406271468352&1709769508298&0&264648564551&287196465468\\136432986329272&49872853461284&35596496016265&43921843131174&1612787339904&35596496016265&27077902295262&1486167648888&27077902295262&49872853461284&10036966091510&0&1486167648888&1612787339904\\810898666012136&295040520004921&210530143593343&260384109402776&9056797748492&210530143593343&160026540442738&8345747917415&160026540442738&295040520004921&58809863948350&0&8345747917415&9056797748492\\4804954366993832&1740921354610008&1241973709508354&1539354236631440&50859539629539&1241973709508354&943391116684990&46866558360269&943391116684990&1740921354610008&343989593164870&0&46866558360269&50859539629539\\28393761930463952&10248546583403267&7309793785660639&9077591498643394&285607822867783&7309793785660639&5548981550039120&263184747962894&5548981550039120&10248546583403267&2008850803107928&0&263184747962894&285607822867783\\167371994534626796&60203605630137598&42932182179508552&53408792169658520&1603864988950885&42932182179508552&32571935843345596&1477945549272391&32571935843345596&60203605630137598&11714105830809598&0&1477945549272391&1603864988950885\end{pmatrix}: \operatorname{Fin}\left(22\right) \to \left(\operatorname{Fin}\left(14\right) \to \operatorname{Int}\right))\left(i\right), \operatorname{HardinA229537StripCertificate}.\operatorname{Z}\left(i\right)\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.7 (powers).**

$$\forall (i: \operatorname{Fin}\left(22\right)), (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{HardinA229537StripData}.\operatorname{T}, \operatorname{Fin}.\operatorname{val}\left(i\right)\right), \operatorname{HardinA229537StripData}.\operatorname{terminal}\right) = \operatorname{HardinA229537StripCertificate}.\operatorname{W}\left(i\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

**Theorem 1.8 (finite_certificate).**

$$(\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (d: \operatorname{Fin}\left(2\right)), (\forall (s: \operatorname{Fin}\left(28\right)), (\sum_{(r: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right))} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, p, r\right) \le \operatorname{Fin}.\operatorname{val}\left(d\right)) \land (\operatorname{HardinA229537StripData}.\operatorname{cl}\left(r, (\operatorname{Fin}.\operatorname{val}\left(d\right)) - (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{HardinA229537StripData}.\operatorname{between}, p, r\right))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{HardinA229537StripData}.\operatorname{T}\left(\operatorname{HardinA229537StripData}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right), s\right))))) \land (\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{HardinA229537StripData}.\operatorname{T}, 14\right), \operatorname{HardinA229537StripData}.\operatorname{terminal}\right) = \sum_{(k: \operatorname{Fin}\left(12\right))} (\operatorname{HSMul}.\operatorname{hSMul}\left((\begin{pmatrix}(-16)&(-16)&196&124&(-741)&(-238)&787&250&(-288)&(-102)&23&6\end{pmatrix}: \operatorname{Fin}\left(12\right) \to \operatorname{Int})\left(k\right), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{HardinA229537StripData}.\operatorname{T}, (2) + (\operatorname{Fin}.\operatorname{val}\left(k\right))\right), \operatorname{HardinA229537StripData}.\operatorname{terminal}\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229537: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229537>.

*Commentary.*

Exact transition counts preserve the remaining defect budget. The continuation vectors obey the square of the proper-colouring sextic after two transitions. The proper-colouring powers and their sextic relation are those of HardinA233177PairTransfer. Natural subtraction is truncated at zero. The transition inequality ensures that the displayed remaining budget is the ordinary nonnegative difference.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.Z`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.cost_relabel`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.finite_certificate`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.one_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.powers`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.zero_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripCertificate.zero_powers`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233125SquareStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/TransferMatrix](../../../../Combinatorics/TraceAvoidingArrays/TransferMatrix.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData](HardinA229537StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../../StripDefects/HardinA229589StripData.md)
