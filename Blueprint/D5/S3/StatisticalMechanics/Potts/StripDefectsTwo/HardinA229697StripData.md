# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Definition 1.1 (Valid).**

$$\forall p: \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (d \le 2)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

Residual budgets are at most two.

**Definition 1.2 (cl).**

$$\forall p: \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(14, \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right): \operatorname{\mathit{Fin}}\left(42\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(28, \operatorname{\mathit{HardinA233177PairTransfer}}.\operatorname{\mathit{cls}}\left((p\left((0: \operatorname{\mathit{Fin}}\left(4\right))\right), p\left((1: \operatorname{\mathit{Fin}}\left(4\right))\right), p\left((2: \operatorname{\mathit{Fin}}\left(4\right))\right), p\left((3: \operatorname{\mathit{Fin}}\left(4\right))\right))\right)\right): \operatorname{\mathit{Fin}}\left(42\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

Positive budgets call the frozen one-defect classifier at d minus one. Zero budget selects the appended equality sector.

**Definition 1.3 (T).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(42\right), \operatorname{\mathit{Fin}}\left(42\right), \mathit{Int}\right)) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{reindex}}\left((\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(28\right), \operatorname{\mathit{Fin}}\left(14\right)\right), \operatorname{\mathit{Fin}}\left(42\right)\right)), (\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(28\right), \operatorname{\mathit{Fin}}\left(14\right)\right), \operatorname{\mathit{Fin}}\left(42\right)\right)), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{fromBlocks}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{T}, \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((\begin{bmatrix}0&0&2&0&2&2&0&2&0&2&2&4&4&4\\1&0&1&1&1&2&1&0&1&2&0&2&2&2\\1&1&1&1&3&1&1&3&3&2&3&2&2&2\\0&0&3&0&1&1&3&2&2&1&1&1&1&0\\2&1&2&0&2&2&4&3&1&2&2&2&2&1\\1&1&2&3&3&1&1&3&1&1&3&2&2&2\\0&0&1&3&2&1&3&2&3&1&2&4&4&4\\2&1&2&1&0&2&4&3&4&2&3&2&2&2\\0&2&1&2&2&3&3&2&2&1&2&1&4&1\\0&1&1&0&2&1&0&2&2&0&1&4&1&1\\1&1&3&1&1&3&2&1&2&0&3&3&3&2\\2&4&2&1&3&2&4&0&1&2&3&2&2&2\\1&2&3&2&4&3&2&4&2&0&1&0&3&3\\1&2&3&1&1&3&2&4&2&1&1&3&0&2\end{bmatrix}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(14\right), \operatorname{\mathit{Fin}}\left(14\right), \mathit{Int}\right)), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{submatrix}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{T}, (\lambda i: \operatorname{\mathit{Fin}}\left(14\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(14, i\right))), (\lambda j: \operatorname{\mathit{Fin}}\left(14\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(14, j\right)))\right)\right), (0: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(14\right), \operatorname{\mathit{Fin}}\left(28\right), \mathit{Int}\right)), \operatorname{\mathit{HardinA233259PairTransferCore}}.\operatorname{Q}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 42 by 42 integer matrix retains HardinA229589StripData.T in its leading 28 by 28 block. The added block records cost two and the inherited cost-one block; its diagonal is the frozen zero-temperature Q. The HardinA229697Strip.finite_certificate theorem pins every transition sum.

**Definition 1.4 (initial).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(42\right) \to \mathit{Int}) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{initial}}, ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 42 integer initial weights append 14 zero entries to the frozen initial vector; HardinA229697Strip.finite_certificate pins the initial class counts.

**Definition 1.5 (terminal).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{terminal}}: \operatorname{\mathit{Fin}}\left(42\right) \to \mathit{Int}) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((\lambda i: \operatorname{\mathit{Fin}}\left(28\right), ((0: \mathit{Int}))), (\lambda i: \operatorname{\mathit{Fin}}\left(14\right), ((1: \mathit{Int})))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 42 integer acceptance weights are zero on the leading 28 states and one on the final 14 states; HardinA229697Strip.finite_certificate pins acceptance at residual zero.

**Definition 1.6 (W).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(18\right) \to \left(\operatorname{\mathit{Fin}}\left(42\right) \to \mathit{Int}\right)) = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((\lambda i: \operatorname{\mathit{Fin}}\left(13\right), (\operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA229589StripData}}.\operatorname{W}\left(i\right), (\begin{bmatrix}0&0&0&0&0&0&0&0&0&0&0&0&0&0\\72&96&156&96&156&156&180&180&156&96&156&180&180&156\\1746&3456&3054&3474&3138&2988&2292&2292&3114&3618&2934&2622&2442&3222\\30924&48744&35172&47100&35832&33678&24318&24870&34944&47652&35532&24396&25524&35856\\377202&540492&374580&522492&355488&367932&259230&239592&361146&532020&363588&215148&239208&345504\\4054452&5457192&3686862&5211834&3253092&3610926&2525088&2178282&3451698&5264016&3399486&1816680&2112798&3097872\\39973590&51600240&34305966&48798738&28515438&33679518&23386752&19142430&31561674&49156692&30342636&14930280&18094416&26725488\\372843774&466758576&307038738&438266286&242741346&302037042&208500144&163815486&278838768&440229924&262043610&120400578&151445256&224364660\\3342906258&4087244490&2668685268&3816926418&2021495418&2629378596&1806309216&1372855800&2399606766&3824917806&2209307268&957022332&1245811218&1846778916\\29096291154&34910163516&22670154966&32461946718&16547751426&22365238494&15302283234&11313015036&20224996710&32467056708&18281788008&7519187418&10105568772&14967598458\\247451918184&292338981054&189060677586&270894647088&133590929976&186719668002&127316871360&91941158790&167598672480&270503213094&149013874584&58514728896&81020012490&119790127116\\2065614317316&2408913672696&1552907898288&2225783676888&1066175027496&1535086607256&1043644310982&738566784198&1369382616810&2219557579812&1199540257290&451729913112&643157973792&948729250602\\16980131833650&19585189731708&12593521657458&18052279830882&8427076665426&12458815447698&8448662417508&5874405151302&11055958421922&17980857343152&9555129230112&3463640377812&5062208619672&7447573600884\end{bmatrix}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(13\right), \operatorname{\mathit{Fin}}\left(14\right), \mathit{Int}\right))\left(i\right)\right))), (\begin{bmatrix}652281782796&652281782796&411865664976&583315212132&171449547156&411865664976&269125207020&142740457956&342899094312&571766819868&228867725556&28709089200&102482976492&131192065692&12384202863618&13379383740726&8470746755316&12147692882022&4741093574478&8421564163788&5619676998942&3466522327950&7230130786548&12011423200110&5695958327742&1489036367916&2759329808262&3969626335902&137797001681994&157434547581540&101023948880442&144809868018546&66058334920422&100011877731162&67669121286324&46325456212050&88353596824416&144091237158360&75431336812758&26402024585970&39549461286348&58020609151800\\4547683011672&4547683011672&2871511262568&4066850776032&1195339513464&2871511262568&1876330385460&995180877108&2390679026928&3986335813104&1595656786176&200158636356&714507277824&914665914180&93083333842296&100021695880896&63314235148212&90721644109164&34826603235192&62971336053900&41961504253914&25643642079258&53951957881452&89652226733676&42077283692256&10678203535194&20297072591748&29031912929826&1106048892585906&1253246019223554&802830682440756&1150664013227322&514113418194570&795266273232756&537021181747404&362600751299580&699838011566478&1143938316227022&590856808948092&200226128199840&306979554317922&449031221260848\\31706267561676&31706267561676&20020063875048&28353924063468&8333860188420&20020063875048&13081701836448&6938362038600&16667720376840&27792576864900&11124856488060&1395498149820&4981516690212&6377014840032&695972433537090&744346421475606&471100660560504&674537552805186&255163223681406&468709981533576&311945331471588&189071393532732&400857958211544&666249514806978&309851853837174&76516601308794&148894633496610&211862182884588&8794257672353454&9892216370803896&6328001981614014&9068118287286906&3976089930378918&6271719447469302&4227648899923026&2819523296751444&5500397675845926&9008033685888456&4596721332083100&1511647900364142&2369015138051208&3454988842925514\\221054853576780&221054853576780&139579099926768&197682446203524&58103346276756&139579099926768&91205111988252&48373987938516&116206692553512&193768755506748&77562062953236&9729358338240&34730938903500&44460297241740&5179968252822366&5517229798952658&3491397300405132&4995879535615698&1865116188714114&3474729580028292&2310066483664662&1389904444389870&2967022365726348&4932294285137778&2275247367471690&547892839804752&1089570177378378&1542999558810870&69349075102647540&77503932231300306&49519675588443210&70947747641475684&30579809402453724&49102568943638778&33046756276934412&21796120317830562&42934562201725776&70428257516407914&35546240666611332&11367038949008328&18187940499564222&26447169852734040\\1541185766835912&1541185766835912&973140008790600&1378234259535888&405094250745288&973140008790600&635878462660308&337261546130292&810188501490576&1350948161465856&540759659975280&67832704614996&242142743445264&309975448060260&38399077909780524&40750452178107012&25784397469456164&36874071048721464&13603999354891812&25668190776902652&17048273202993654&10190291415759630&21886928450202132&36390310232378544&16664518445132844&3920437685330514&7955375443002648&11217217602612366&542911141731655692&603251993091531096&385043727395666592&551532971976560136&234021853277252496&381963419824024440&256700030028357762&167612398299530154&333091756681103898&547149893538619548&273403680032385738&85171608454963284&138989625376493160&201517452818736678\end{bmatrix}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(5\right), \operatorname{\mathit{Fin}}\left(42\right), \mathit{Int}\right))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 18 by 42 integer table appends the new sector to the first 13 cached rows of HardinA229589StripData.W, then tabulates the remaining rows. HardinA229697StripForward.forward_certificate pins its initial row, every successor row, and its polynomial relation.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](../../../Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../StripDefects/HardinA229589StripData.md)
