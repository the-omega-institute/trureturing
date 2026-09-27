# Reverse-pivot elimination bounds every law in G

A fixed numerical multiplicity profile gives an all-query bound for EVERY law in [report534](534-one-entropy-budget-controls-every-pure-prime-chain.md)'s G. The proof assigns each selected mixed query to its largest prime in a chosen order, integrates in reverse order, retains the original pure-cylinder subtraction, and cancels one entropy budget. It never projects mixed original classes into a purported disjoint pure family.

The three profiles below give the strict bounds 10.440528023, 11.01370314 and 11.004239809, respectively, below T=565/51. These are ordinary mathematical results with a newly reconstructed rational/Taylor consumer; no Lean verification is claimed.

The existential target for these sparse profiles is already covered by [report539](539-a-weighted-mixed-inventory-certifies-one-entropy-law.md)'s weighted-mixed-capacity criterion. The additional conclusion here is the bound for every nu in G, together with its explicit order-dependent profile criterion. This is not a first noncoverage result for those sparse inputs, and it does not resolve the general shallow-mixed core or unrestricted Erdős #7.

## Original core, queries and one entropy law

Use P={3,5,7,11,13,17,19}, product Haar probability H, and one finite irredundant actual distinct-modulus core M0 with complete survivor U. All original phases stay fixed. Every removed original label remains unused relative to M0. Put

    alpha=7235955529/6075000000000, Lambda=1/alpha,
    q_d(nu)=max_a nu([a]_d),
    R_P(nu)=sum_(nonunit P-smooth d)q_d(nu).

As in reports530 and534, G consists of probabilities supported on the same full U such that

    nu<=Lambda H,
    R_unused(nu)+D_H(nu)<=log Lambda.             (PP1)

Unused labels include every depth outside the global numerical core. Pure originals at each prime are disjoint: otherwise a nested one would be redundant. This argument is used only for globally pure original classes.

Fix any total order on P and define pi(d) as the last prime dividing d. Write

    d=pi(d)^j(d)*dbar,

where all primes of dbar precede pi(d). Use B=10^9 and head depths

    (n3,n5,n7,n11,n13,n17,n19)=(8,7,7,7,7,7,7).

For 1<=j<=n_p let m_(p,j) count the shallow mixed original labels d<=B with pi(d)=p and j(d)=j. Let T_order be the remaining shallow mixed original labels whose pivot exponent exceeds n_(pi(d)). Every original numerical label is retained in exactly one category; the profile does not merge distinct cofactors.

## A one-coordinate profile moment

For nonnegative integer multiplicities m=(m1,...,mn), let s_k=sum_(j<=k)m_j and s_0=0. Define

    K_(p,n)(m)=sum_(k=0)^(n-1) [(p-1)/p^(k+1)] exp(k+s_k)
               +p^(-n) exp(n+s_n)
               -sum_(j=1)^n p^(-j).             (PP2)

At m=0 this is exactly report534's pure-chain moment M_(p,n).

Let E be any subset of {1,...,n}. For j in E let C_j be pairwise-disjoint original pure depth-j cylinders and A_j arbitrary depth-j query cylinders. At depth j allow an additional multiset of at most m_j arbitrary query cylinders. Then

    integral_(Z_p minus union_(j in E) C_j)
       exp(sum_(j in E)1_(A_j)+sum_(all extras B)1_B) dH_p
      <=K_(p,n)(m).                              (PP3)

To prove it, expand exp(1_A)=1+(e-1)1_A for every query occurrence. Repeated occurrences are retained separately. A nonempty intersection of prefix cylinders has mass at most p^(-maximum depth). Thus every nonnegative expansion term is bounded by the corresponding term for a nested query family. On the disjoint original union the integrand is at least one, allowing subtraction of exactly sum_(j in E)p^(-j).

Missing pure depths may be filled in this NUMERICAL upper expression. Inserting a depth-t query and the additional subtraction p^(-t) increases it by

    (e-2)p^(-t)
      +sum_(nonempty prior occurrence subsets S)
         (e-1)^(|S|+1)*p^(-max(depths(S),t))>0.

No new actual original class is introduced. Filling any missing additional-query slots also increases the expression. For a fully nested profile, the annulus of mass (p-1)/p^(k+1) has load k+s_k, and the terminal cylinder of mass p^(-n) has load n+s_n. This gives PP2 after the formal full pure subtraction. In particular K is positive and increases when any prefix sum s_k increases.

Moving an additional query from a later depth b to an earlier depth a<b increases s_k by one exactly for a<=k<b. The change in K is

    (e-1)*sum_(k=a)^(b-1) [(p-1)/p^(k+1)] exp(k+s_k)>0.

Thus two occupied extra layers with at most one query per layer are worst at depths 1,2; one extra layer is worst at depth 1. This is a general prefix-sum comparison, not a scan of layer placements.

## Reverse-pivot gluing keeps the selected phases fixed

Fix any nu in G. For every occupied head query select one full residue cylinder A_d attaining q_d(nu), once for the proof. For a mixed d=p^j*dbar the selected cylinder has CRT factors

    A_d=B_d times A_(d,p),

where B_d uses only coordinates before p and A_(d,p) is a depth-j p-cylinder. These two factors come from that SAME full maximizing phase; they are not optimized separately.

For each p let E_p be the occupied pure depths at most n_p and D_p the complement of their actual pure originals. Set D=product_p D_p. Then U is contained in D. Passing from U to D discards mixed original restrictions only as an upper bound on the partition-function domain; pure originals beyond the selected heads are also omitted from this larger domain and will have their queries paid by the density tail. U itself and the source law never change.

Let f be the sum of the selected occupied pure-head query indicators and the selected shallow mixed-head query indicators. Split f=sum_p f_p by pivot. Each f_p depends only on p and its preceding coordinates.

Integrate the last coordinate first. With every preceding coordinate y fixed, the extra depth-j pivot queries active on this fibre are exactly those with y in B_d, at most m_(p,j). The domain in that coordinate is D_p, so PP3 bounds this integral by K_(p,n_p)(m_p), uniformly in y. Pull out this constant and repeat in reverse pivot order. Fubini gives

    integral_U exp(f)dH
      <=integral_D exp(f)dH
      <=product_p K_(p,n_p)(m_p).                (PP4)

No mixed original is claimed to remain irredundant or disjoint in a cofactor fibre. The only red-cylinder subtraction comes from the actual globally pure core. All mixed query occurrences remain counted separately.

The entropy inequality on the ORIGINAL U gives

    E_nu f-D_H(nu)<=log integral_U exp(f)dH
                   <=sum_p log K_(p,n_p)(m_p).

Add PP1 to cancel the SAME single entropy term. The remaining occupied queries are pure powers beyond n_p, mixed labels above B, and labels in T_order. Under nu<=Lambda H these have the simultaneous upper bound

    Lambda*[sum_p 1/(p^n_p*(p-1))
            +tau_mixed(B)+sum_(d in T_order)1/d].

Consequently EVERY nu in G satisfies

    R_P(nu)<=log Lambda+sum_p log K_(p,n_p)(m_p)
       +Lambda*[tau_mixed(B)+sum_p1/(p^n_p*(p-1))
                  +sum_(d in T_order)1/d].       (PP5)

The reciprocal envelopes may include unused labels as an overestimate of the remaining occupied contribution; no equality of these envelopes with the occupied inventory is asserted. Their infinite sums converge. The selected head inventory is finite, while the full query conclusion follows by taking finite subsums and monotone convergence. No original-height cutoff is imposed on U.

## The sufficient profile criterion and its quantifiers

Write M_p=M_(p,n_p) and

    Gamma_order=sum_p log[K_(p,n_p)(m_p)/M_p]
                  +Lambda*sum_(d in T_order)1/d.

Report534's retained base bound is strictly below C=4522277/500000=9.044554. Therefore

    R_P(nu)<C+Gamma_order   for every nu in G.

An order with Gamma_order<delta=51863873/25500000 suffices. The order may depend on the fixed numerical core, and this robust count criterion then holds for every law in G. Examining different orders is a possible finite certificate operation for that core, not a uniform solution of all original families. No prime-order scan is performed here.

For the already selected maximizing phases one may instead use

    msharp_(p,j)=sup_y #{d in the (p,j) head: y in B_d}.

The same scalar theorem holds with msharp: at every actual integration fibre it simultaneously bounds the number of active occurrences. Its entries, and hence its resulting bound, can depend on nu and on the fixed choice of its maximizing phases. Counts at different depths need not attain their maxima at the same y; that merely makes this a conservative envelope.

A distinct, unfinished refinement would retain the nonconstant local factor. At the last pivot one has the valid inequality

    integral_D exp(f)dH
       <=integral_(D_before) exp(sum_(earlier pivots)f_p(y))
             K_(last,n_last)(m_last(y)) dH_before(y).           (PP6)

The factor K(m_last(y)) is now a weight in the next coordinate integration. PP3 is unweighted and cannot simply be reapplied to that expression. One must retain this full joint weighted integral, dominate the weight, or prove an additional weighted lemma. No closed recursive scalar bound for this nonconstant refinement is claimed.

## Three explicit natural-order profiles

Take 3<5<7<11<13<17<19. The following strict logarithm bounds are independently certified by positive Taylor sums:

    log K_(3,8)(0)<1.342392,
    log K_(5,7)(0)<0.400451,
    log K_(7,7)(0)<0.210347,
    log K_(11,7)(0)<0.102076,
    log K_(13,7)(1,1,1,1,1,1,1)<0.709769,
    log K_(17,7)(1,1,1,1,1,1,1)<0.470204,
    log K_(19,7)(1,1,1,1,1,1,1)<0.401435.

Their sum is 3.636674. The retained constants are

    log Lambda<6.732875,
    base density tails<0.070979023.

First suppose every shallow mixed core label has pivot in {13,17,19}, with at most one label in each exponent layer. Every shallow mixed label with such a pivot has exponent at most 7, because 3*p^8>B. The three all-one length-7 profiles therefore dominate the actual heads and there is no shallow pivot tail. PP5 yields

    R_P(nu)<10.440528023=10440528023/1000000000
                  <565/51,  for every nu in G.    (PP7)

There are at most NINETEEN actual shallow labels in this class: 7 at pivot 13, 6 at pivot 17 and 6 at pivot 19. Indeed 3*17^7>B and 3*19^7>B. The 21 slots in the three displayed comparison profiles include two impossible shallow slots; using them is a safe relaxation, not an assertion that 21 such shallow originals can occur.

Second, retain these high-pivot conditions, allow no shallow 5- or 7-pivot labels, and allow at most two occupied 11-pivot head layers with at most one label in each. Their worst profile is (1,1,0,0,0,0,0), with

    log K_(11,7)(1,1,0,0,0,0,0)<0.675246.

Shallow 11-pivot labels beyond exponent 7 are unrestricted. Their complete numerical reciprocal inventory, even allowing all heights and all earlier cofactors, is

    tau_11=[(3/2)*(5/4)*(7/6)-1] *sum_(j>=8)11^(-j)
          =19/(160*11^7)=19/3117947360.

Its density payment Lambda*tau_11 is strictly below 0.000005117. This envelope deliberately also includes labels above B already paid in the base mixed tail, so any overlap is conservative. Then

    R_P(nu)<11.01370314=550685157/50000000
                 <565/51,  for every nu in G.     (PP8)

Third, retain the high-pivot conditions, allow no shallow 5-pivot labels and no 11-pivot head label, and allow at most one 7-pivot head label. No restriction is imposed on shallow 7- or 11-pivot labels beyond exponent 7. The worst 7 profile is (1,0,0,0,0,0,0), with

    log K_(7,7)(1,0,0,0,0,0,0)<0.773905.

The complete 7-pivot reciprocal tail is

    tau_7=[(3/2)*(5/4)-1] *sum_(j>=8)7^(-j)
         =1/(48*7^6)=1/5647152.

The same density payment Lambda*(tau_7+tau_11) is below 0.000153786, giving

    R_P(nu)<11.004239809=11004239809/1000000000
                  <565/51,  for every nu in G.    (PP9)

The tail cofactor products omit 1 because these are mixed labels. They sum complete numerical labels, not independently selected cofactor phases. All pure original heights, all unused query heights and all actual deeper mixed constraints remain present throughout the three statements.

## Increment over the existing existential criterion

All three explicit classes already meet report539's weighted capacity threshold v<=2/3. For a high pivot p and one selected label at exponent j, its saturated weighted cap is at most

    (2/3)*[(p-1)/(p-2)]*p^(-j),

because the nonunit earlier cofactor has weighted cap at most 2/3. Summing all allowed layers bounds the high contribution by

    sum_(p=13,17,19) 2/[3*(p-2)].

The second profile adds at most (2/3)*(10/9)*(1/11+1/121), plus the complete 11-pivot tail weighted by D_max=4096/935. The third adds at most 4/35, plus the complete 7/11 tails weighted by D_max. All also include D_max times the original deep reciprocal tail. The new consumer checks that each of these explicit bounds is below 2/3.

Thus their existence of a good complete survivor-Haar law is already available. PP7--PP9 say more about the permitted source laws: every nu satisfying the original G conditions obeys the displayed total-query bound, regardless of its actual optimizing phases. Neither report539's existence statement nor a product of the separate mixed-chain bounds in [report535](535-mixed-chain-moments-retain-shared-prime-correlations.md) supplies that universal conclusion.

## Exact verification and remaining gap

The [fixed consumer](../../frontier/cover-geometry/mixed_pivot_profile.py) and its [result](../../frontier/cover-geometry/mixed_pivot_profile.json) read two pinned existing results: [pure_chain_entropy.json](../../frontier/cover-geometry/pure_chain_entropy.json) from report534 and [phase_resampling_arithmetic.json](../../frontier/cover-geometry/phase_resampling_arithmetic.json) from report530. It uses the retained upper e bound, verifies it by a degree-36 positive Taylor tail, bounds each K by substitution of that e upper bound, and certifies log K<L by a degree-50 lower Taylor sum for exp(L). All positivity conditions and the zero-profile agreement with the retained pure moments are checked.

The base density tail is reconstructed from the two retained inputs, using all pure and mixed geometric tails, and is required to equal the retained exact value. The complete 11/7 pivot tails, the three assembled strict rational bounds and their margins, the corrected actual slot count, and the prior existential capacity comparison are all checked. One new execution completed with 55 successful checks. No original-family enumeration, prime-order scan, label-inventory producer or Lean build was run.

What remains unresolved is a sufficiently small profile or a valid phase-sensitive weighted estimate for arbitrary actual irredundant cores. A large robust Gamma does not refute existence of a good law or yield a lower witness: it can result from replacing actual cofactor activation by worst-case multiplicity. Likewise the unweighted lemma alone does not close PP6's weighted recursion. These are limits of this sufficient bound, not counterexamples to the target.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/mixed_pivot_profile.py
```
