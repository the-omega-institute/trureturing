# Digit injections transport free-endpoint heads and common sources

The head and only-large-owner conclusions of [Report626](626-free-square-roots-admit-one-complete-boundary-gate.md) and [Report627](627-secondary-pair-endpoints-admit-a-same-source-release-budget.md) transfer to any ten ordered odd head primes, with their coordinate-relative endpoint and mixed-inventory restrictions. Independently uniform digit injections also transport one actual joint source, its joint prefix caps, and its complete unit-inclusive query gate under the explicit source hypotheses below. These are ordinary mathematical deductions, not new Lean verification or a resolution of unrestricted Erdős #7.

| Head interface | Head Haar lower bound | Extendible-head lower bound with only-large-owner network |
| --- | ---: | ---: |
| Report626 free seven-star roots; twelve labels share one pair per edge | >1/42000 | >1/44000 |
| Report627 also frees eight secondary labels on the sixth/seventh head-coordinate edge | >1/210000 | >1/262000 |

Every network owner is a prime at least2^115, distinct from the head primes. Each actual listed parent is smaller than its owner. The assigned-inventory, distinct-label, globally fixed-phase and no-extra-small-owner/private/TypeI conditions remain. Owners need not exceed unused head primes.

The proof reuses [Report592, section 5](592-joint-second-moment-extends-cubic-tails-to-ten-primes.md). Its additional obligation here is to show that Report626's endpoint relations, and not only its exponent inventory, survive every nonempty pullback.

## Exact target family and criterion

Write

    p=(3,5,7,11,13,17,19,23,29,31),
    r_1<...<r_10 any ten odd primes.

Thus r_i>=p_i. Let the target family be finite, with distinct numerical moduli supported on the r_i and one fixed residue for each original. Interpret Report626's retained labels by their coordinate exponent vectors: central coordinates are r_1,r_2, the five star/pair coordinates are r_3,...,r_7, and the unrestricted continuation coordinates are r_8,r_9,r_10. All pure originals, star phases and square-star first roots are arbitrary at their finite heights. On each of the ten edges among r_3,...,r_7, the twelve retained labels that are present share one first-digit endpoint at each coordinate. Other mixed labels supported on the first seven coordinates satisfy Report626's unchanged maximum-exponent / central-exponent / support-size disjunction. Missing retained labels remain allowed.

The transfer criterion is checked below for EVERY fixed injection: each nonempty pulled-back original is one cylinder with the same full exponent vector; distinct numerical labels remain distinct; all present endpoint-sharing relations persist; and a uniform reference lower bound holds before any averaging. The final finite average must equal target Haar, not merely a favourable target law.

Choose heights H_i resolving every target original, increasing them to at least two when needed. Write X_p=product_i{0,...,p_i-1}^{H_i} and X_r=product_i{0,...,r_i-1}^{H_i}, equipped with uniform product measures. These are CRT prime-power digit coordinates; no ring homomorphism between unequal primes is claimed.

## One fixed injection preserves the complete admissible family

For every i and digit j<H_i choose a shift s_ij in Z/r_i Z. Define

    F_s(x)_ij = x_ij+s_ij mod r_i.

Because p_i<=r_i, every coordinate digit map is injective. The same F_s is used for the whole family, all overlaps, and all retained roles.

A target cylinder fixing the first e_i digits at coordinate i has empty preimage if any fixed digit misses the corresponding injection image. Otherwise those digits have unique preimages and the result is exactly one source cylinder fixing the first e_i source digits. In particular an exponent is neither decreased nor replaced by a union of cylinders. CRT gives one source residue modulo product_i p_i^{e_i}.

Two distinct target numerical moduli have distinct exponent vectors, hence their nonempty preimages have distinct source numerical moduli. Each has only the single preimage residue determined by its original target residue and the same F_s. No independent phase choice is made per branch or per query.

For one retained edge suppose all its present target labels share endpoints d_i,d_k. If either common endpoint misses the relevant first-digit injection image, every such target label has empty preimage. Otherwise every nonempty pulled-back label has the same pair of unique inverse endpoints. Some labels can still disappear because a central or second outside digit misses an image. This removes slots but cannot split the common endpoint pair. All missing slots can be padded once using that pair, as Report626 permits. If no live label remains, choose one auxiliary pair once. A pair already null under the actual pure source can be replaced by the auxiliary live rectangle using Report626's stated source-null reduction. These are extra restrictions, not alterations to any surviving original phase or numerical label.

The pure and star phases of the pullback are arbitrary, which is exactly Report626's allowed scope. The square-star roots can be any first digits, so their pullbacks impose no new anchor obligation. Every inventory condition depends on the preserved exponent vector and coordinate roles. Originals touching one of the last three coordinates still do so. The pulled-back family is therefore admissible for the reference Report626 theorem for every s.

Let U be the target survivor and h=18854797422716739/778672375572358758400. The source survivor is EXACTLY F_s^{-1}(U): empty original preimages need no deletion, and the nonempty ones are precisely the pulled-back family. Auxiliary deletions used in its proof may only shrink a constructed witness. Consequently

    H_p(F_s^{-1}(U)) >= h > 1/42000       for every s.

No query-dependent selection or optimization enters this statement. For each fixed s, the reference theorem constructs its own single source for that one pulled-back family; the conclusion being averaged is its Haar survivor bound.

## Finite averaging restores target Haar exactly

Choose all shifts independently and uniformly. For every fixed source point x, each F_s(x)_ij is uniform on the r_i-symbol alphabet, and all target digits are independent. Thus F_s(x) has exactly H_r law. Finite double counting gives

    H_r(U)
      = E_s E_(x~H_p) 1_U(F_s(x))
      = E_s H_p(F_s^{-1}(U))
      >= h > 1/42000.

The family and heights were arbitrary finite choices. No uniform maximum height or number of originals was introduced. No infinite-limit interchange is required. This proves the stated transfer.

Report624's sentence declining an arbitrary-head-prime transfer records its published scope. It is not a counterexample or an impossibility claim. The argument above supplies the previously unstated stability bridge for the broader phase scope of Report626.

## Keeping outside coordinates and existential extensions

The same proof applies directly to Report626's only-large-owner consequence, without transporting its query norm. Require each target outside owner to be a prime at least2^115, distinct from the ten target head primes. Keep its numerical prime and digits unchanged. Every parent union is fixed and finite, using target head coordinates or earlier declared owners that are numerically smaller than this owner; every non-head original is either a pure owner power or an assigned mixed owner original. There are no additional small owners, private blocks or Type I blockers.

Choose the head resolving heights to cover the head exponents of every actual original, including all owner-assigned mixed originals. Use F_s on the head and the identity on all outside coordinates. Every nonempty pullback still has the same head and owner exponent vector. Reference head primes are at most31 and all outside owners are unchanged and at least2^115, so no numerical prime collision or parent-order violation is introduced. Owner identity, global phases, declared parent unions, distinct original labels and exclusive inventory assignments persist. Some originals disappear, which is allowed; unused declared parents do not create new originals. The full pulled-back family therefore satisfies the reference only-large-owner theorem for every s.

Let

    E_r={y in target head: there exists an outside z with (y,z) in U},
    E_s={x in source head: there exists an outside z with (F_s(x),z) in U}.

The outside coordinates and their resolving heights are identical, so

    E_s=F_s^{-1}(E_r).

Report626 gives H_p(E_s)>1/44000 uniformly (indeed its same explicit stronger rational lower bound applies). Averaging yields H_r(E_r)>1/44000. If Q_off is the product of the actual outside resolving prime powers, each extendible target head class has at least one actual outside assignment. Therefore the full target survivor density is greater than1/(44000 Q_off).

An owner need not exceed an unused target head prime. Every listed target head parent is smaller than its owner by the interface, and its source image is at most31, while the owner remains at least2^115. Head coordinates unused by that owner do not enter its assigned originals. The ten distinguished head primes need not be the ten smallest primes in the entire target family.

This extension uses only pullback stability and existential projection. It does not infer a target query-law identity from Haar averaging, and it does not transfer a separate network fee or any undeclared interface.

## The eight-secondary-label release obeys the same stability check

Report627 proves the eight-secondary-label theorem for reference edge{17,19}; its coordinate-relative counterpart on target edge{r_6,r_7} also transfers. Only the four linear pair labels on that edge must share their first endpoints; its eight square-linear labels have arbitrary first roots. Both requirements survive pullback by the argument above. The other nine edges retain their usual shared pair.

Hence that reference theorem's head bound >1/210000 and only-large-owner extendible-head bound >1/262000 transfer with the same target and outside assumptions. This uses Report627 as a separate premise; it does not attribute the secondary-label release to Report626.

## A general transport of one actual joint source

The following stronger construction is not needed for the direct Haar/projection argument above. Its source hypothesis is material: every pulled-back family must provide one measure satisfying all the declared bounds together. Separate favourable measures chosen for different queries do not meet it.

### Finite model and one source per injection

Let p_i<=r_i and fix finite heights H_i. Let X_p and X_r be the corresponding products of digit alphabets. A random map F adds an independent uniform shift modulo r_i at every coordinate digit to the p_i-symbol source alphabet. Each digit map is injective.

Fix one target family and let U_r be its survivor. For every F suppose one nonnegative finite measure eta_F on X_p has been constructed, supported on F^{-1}(U_r). These choices are made once for each F, before choosing any query. They may depend arbitrarily on F and on the whole pulled-back family. Since the injection set is finite, the following is a single well-defined target measure:

    nu(A)=E_F eta_F(F^{-1}(A)).                         (ST1)

It is supported on the actual target survivor. All statements below concern this same nu.

### Mass and full Haar domination

If eta_F(1)>=m uniformly, then nu(1)>=m. If eta_F<=C H_p uniformly, then for any A,

    nu(A)<=C E_F H_p(F^{-1}(A))=C H_r(A).              (ST2)

The last equality is exact finite digit averaging. The dependence of eta_F on F causes no difficulty because the pointwise domination is used before averaging.

### Joint prefix caps

For a coordinate set J and positive depths e_i<=H_i suppose every simultaneous source prefix cylinder satisfies

    eta_F(C_(J,e)) <= c_J product_(i in J) p_i^(-e_i)  (ST3)

uniformly in F and in every prefix value. This is a joint cylinder bound, not a collection of marginal bounds.

Fix one target prefix cylinder A with the same depths. Its preimage is empty or one source prefix cylinder. For a single target digit, exactly p_i of the r_i uniform shifts put that digit in the injection image. The shifts are independent, so

    Pr_F(F^{-1}(A) nonempty)=product_(i in J)(p_i/r_i)^e_i.

Combining this event with ST3 yields

    nu(A)<=c_J product_(i in J) r_i^(-e_i).            (ST4)

In particular c_J=product_(i in J)c_i is preserved as the same joint prefactor. One must not multiply independently proved marginal bounds to obtain ST3. In the Report626 application it is supplied by product-core domination and reverse integration of normalized head rows before the final restriction; restricting further preserves it.

### The complete unit-inclusive query gate

At the fixed heights index queries by exponent vectors e with0<=e_i<=H_i, including the all-zero vector. For each exponent vector a layout b chooses one target prefix cylinder C_(e,b_e). Put

    L_b=sum_e 1_(C_(e,b_e)),
    Gamma_r(nu)=max_b integral L_b^2 dnu.

Define Gamma_p analogously on the source exponents. For one fixed b and F, every query preimage is empty or one source cylinder with that same exponent vector. Because different exponent vectors remain different numerical source query labels, the resulting partial layout can be completed to one full source layout by choosing arbitrary cylinders for the missing labels. All indicators are nonnegative, so pointwise

    L_b composed with F <= L_(completed source layout).

The unit query is never missing. Therefore

    integral L_b^2 dnu
      =E_F integral (L_b composed with F)^2 deta_F
      <=E_F Gamma_p(eta_F).

The right side is independent of b, and hence

    Gamma_r(nu)<=E_F Gamma_p(eta_F).                  (ST5)

For fixed0<=c<1, any uniform source gate

    eta_F(1)-c Gamma_p(eta_F)>=gamma

therefore gives the same target gate

    nu(1)-c Gamma_r(nu)>=gamma.                      (ST6)

No interchange of maximum and average as an equality is used. No compatible joint assignment of all query phases is assumed. A complete query layout already permits unrelated phases at its different numerical labels, exactly as in Report592/598's definition.

This transports the actual unit-inclusive Gamma, not a claim that the numerical L/W coefficient arrays are unchanged at larger primes.

### One measure for every finite query height

For an actual finite family choose H0 large enough to resolve all originals and any auxiliary deletions needed to construct its source. For each of the finitely many injections F0 through H0, select ONE reference measure eta_F0 that satisfies the claimed reference bounds for all finite query heights, as the relevant reference theorem requires. An existence statement supplying a different measure separately for each query height would not suffice here.

For a larger query height H, independently average additional digit shifts while using the same eta_F0, with its own consistent source marginals. The resulting target finite marginals are consistent. In fact averaging each extra target shift makes its image digit uniform independently of every earlier digit and of the sampled source point. Thus the target measure is simply its H0-digit marginal extended with independent Haar digits above H0. This describes one target measure explicitly, without selecting a new source per query.

Apply ST2--ST6 at each finite H to that measure. Every finite query and every joint prefix bound is then supported by the same target law. The finite input and its globally fixed original phases never change.

### Intended scope of application

For the full ten-prime supported survivor submeasures of Report626, the uniform mass and joint prefix caps can be transported by ST1--ST4 after the pullback-stability proof. Its root-independent actual core sources also supply the unit-inclusive gate on the first seven coordinates, so ST5--ST6 apply there when that specific core family and its simultaneous all-height source are selected.

These facts can supply hypotheses to a separate network theorem. They do not automatically assert that a particular target inventory, owner ordering, conditional kernel or fee accounting is admissible. For the already stated only-large-owner family, the simpler F on head and identity on owners argument transports its extendible-head conclusion directly and avoids those additional obligations.


## What has and has not been transported

The direct survivor and existential-extension statements need only an admissible family for every fixed injection and a uniform reference Haar bound. The stronger source statement needs the joint source hypotheses stated in ST1--ST6. It preserves inequalities, not equality of query laws or numerical coefficient tables.

For the ten-prime supported measures obtained from Reports626/627, the full density cap is C=110656/2673. The joint prefix prefactors indexed by the ordered reference coordinates are

    (2,4/3,7/5,11/9,13/11,17/15,19/17,5/3,20/11,2).

ST4 replaces every reference-prime denominator by its target-prime denominator while retaining the joint prefactor. The unit-inclusive gate is asserted on the coordinate set on which the reference theorem supplies that gate; in particular the seven-coordinate core gate is not silently relabelled as a ten-coordinate gate.

The transport does not remove endpoint-sharing requirements or missing mixed-inventory classes. It does not admit arbitrary smaller owner networks or additional private interfaces. Further uses must check their own inventory, ordering, normalization and fee hypotheses.

Independent finite checks of prefix pullbacks, common endpoints and joint Haar averaging supplement the ordinary proofs. They do not establish the universal quantifiers by enumeration, and no new large source scan is needed: the universal statements follow from the digit injection, unique-prefix and finite-average identities above.

The [portable checker](../../frontier/cover-geometry/head_digit_injection_transport.py)
and [exact data](../../frontier/cover-geometry/head_digit_injection_transport.json)
retain 222 named checks, including 19,574 prefix cases, 42,875 joint-edge
cases, a complete joint Haar average, and a counterexample showing why an
arbitrary whole-quotient injection need not preserve prefixes. It verifies
the existing Report626 certificate's producer and kernel hashes without
rerunning its large scan. Its finite scope is the head-prefix transport;
ST1--ST6 and the network projection are established by the ordinary
arguments above, not by those finite checks.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/head_digit_injection_transport.py
