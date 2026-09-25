# A common joint source admits all late-four high mixed supports

Let P={3,5,7,11,13,17,19}, Q=P minus{3}, and L={11,13,17,19}. Take any finite actual family with pairwise distinct odd nonunit P-smooth numerical moduli, arbitrary fixed residues and arbitrary finite heights. Allow every pure prime power, every rooted star3^a p^b, every rooted triangle3^a p^b q^c, every non3 pair tower in

    E9={(5,7),(5,11),(7,17),(7,19),(11,17),(11,19),
        (13,17),(13,19),(17,19)},

and every non3 support S contained in L with |S|>=3. The last clause permits all four triple towers and the full quadruple tower, with every positive exponent vector.

There is one probability rho on its complete actual survivor U with

    R_P(rho)<=224167587171895144296993552278596972445671925
                 /19408569499185259521646920039976279342177201
             =11.549928354137863... <566/49.             (HG1)

Arbitrary further distinct originals touching23 or29, with arbitrary P-smooth cofactors, phases and finite heights, still leave actual Haar survivor mass at least

    346188371998272899824226991774152611457147
      /502170033174842537440748281763576137215360000000
      =0.0000006893847683613951... >1/1500000.          (HG2)

This enlarges Report570's support class; its stronger earlier numerical constants remain valid on that smaller class. The theorem neither requires root-prefix freedom nor selects projected phases. It does not include arbitrary rooted supports of size>=4 or the missing non3 pair towers. It is ordinary mathematics and exact rational computation using existing comparison and kernel constructions, not new Lean verification or a claim of external novelty.

## 1. One actual normalized source

Use the complete actual pure-p survivor as each coordinate base. Its normalized law gives cylinder caps (p-1)/[(p-2)p^e]. Assign every actual mixed original to its largest prime q and form its actual forbidden union A_q at each complete previous history. Apply Report561 AR3's normalized distortion kernel with

    (t5,t7,t11,t13,t17,t19)=(0,1,3,4,5,7),
    delta_q=t_q/(q-2).

This gives one normalized joint law mu, including the histories with entirely forbidden fibres. Its full-past cylinder caps and global Haar density bound are

    (C3,C5,C7,C11,C13,C17,C19)
       =(2,4/3,3/2,5/3,12/7,8/5,9/5),
    mu([r]_(q^e)|past)<=Cq/q^e,
    dmu/dH<=Lambda=product Cp=1152/35.                (HG3)

Every later normalized row preserves the probabilities of previously assigned events. The actual phase of every original remains fixed; no auxiliary height law is substituted for the actual source.

Write independent comparison heights Kp with Pr(Kp>=j)=Cp/p^j, j>=1, and gp=EKp=Cp/(p-1). The exact cofactor inventories for rows5,7,11,13 are Report570 PG1. Row17 adds one product K11*K13 to that inventory, corresponding to the new support{11,13,17}. Row19 adds

    K11*K13+K11*K17+K13*K17+K11*K13*K17.

Thus explicitly

 M17=K3(1+K5+K7+K11+K13)+K7+K11+K13+K11*K13,

 M19=K3(1+K5+K7+K11+K13+K17)+K7+K11+K13+K17
       +K11*K13+K11*K17+K13*K17+K11*K13*K17.        (HG4)

For every fixed current q-exponent, numerical uniqueness gives at most one original per full old cofactor. The different support monomials enumerate disjoint numerical label patterns. Apply conditional convex comparison to the actual labelled cylinders under the same previous marginal, before completing to these inventories. The existing normalized-kernel argument then yields

    mu(Aq)<=bq=E(Mq-tq)_+/(q-2-tq),
    s=mu(U)>=1-sum_q bq.                            (HG5)

The original events need not be independent, and the actual final mu differs from the old source because its17 and19 forbidden unions include the new supports. Bounds are not added across different optimizing laws.

## 2. Exact low events retain every height

For any nonnegative integer-valued M,

    E(M-t)_+=EM-t+sum_(m<t)(t-m)Pr(M=m).             (HG6)

The means in HG4 are evaluated by independence of the auxiliary heights, replacing each Kp monomial by the corresponding product of gp. This retains the entire high tail. At K3=0, K5 integrates to one in rows17 and19 and every other active variable has a positive linear coefficient. At K3=k>0, every previous Q coordinate has a positive linear coefficient. Therefore the events M<t involve finitely many values of every active coordinate, even with the new interaction terms. Exact finite enumeration of these low events together with the full mean computes HG6 without truncating a positive tail.

The charges are

    b5=1/3,
    b7=41/180,
    b11=920489/11907000,
    b13=50909297/1375258500,
    b17=47451950714518818239/1248839143114168856250,
    b19=380494401503206437545347690294799713
          /15004063730351506037395086038432812500.

Consequently

    s>=s0=7838365711219648132666311015826216699
             /30008127460703012074790172076865625000
          =0.26120809175728604... .                  (HG7)

The full query includes every nonunit P-smooth modulus, not only the original support inventory. Its auxiliary load with the unit included is V=product_p(1+Kp). The same full-mean and exact low-product calculation gives

    B=E(V-6)_+
      =110858473194725664986233638097168
         /64795630020766937106234185390625
      =1.7108942865312928... .                        (HG8)

## 3. Complete queries and actual continuation

Set sigma=mu restricted to U, of mass s. For each finite query box choose all phases maximizing under this same sigma, and include the unit in L. The pointwise inequality L-1<=5+(L-6)_+ and the same-source conditional comparison give

    R_P(sigma)<=5s+B.

Cofinal exhaustion gives the full all-height result because every term is nonnegative and the auxiliary first moment is finite. This uses the conditional caps of mu before deletion; it does not carry them through final conditioning. Dividing by s proves HG1. Before normalization the strict margin is

    566s-49R_P(sigma)>=321s0-49B
      =346188371998272899824226991774152611457147
         /24767698132439755831791956763118299065625000
      =0.013977414055480957... >0.                    (HG9)

Independently condition23 and29 Haar on their actual complete pure-power survivors. Their positive-height query sums are at most1/21 and1/27, and their density product is at most616/567. Arbitrary mixed additional labels have total charge at most

    R_P(sigma)/21+R_P(sigma)/27+[R_P(sigma)+s]/567.

The old unit contributes the actual mass s in the final term. The remaining submeasure has mass at least HG9/567, and density at most Lambda*616/567. Dividing gives HG2. This continuation asserts survival/Haar mass, not the preservation of the seven-prime query bound by the newly conditioned nine-prime law.

## 4. The integrated supports improve on a later union charge

Keep exactly the final caps HG3 but construct only the old E9 plus rooted triangle source. Its old survivor reserve is

    s_base=1138658364206362881832578372012329707
              /4286875351529001724970024582409375000.

The cap sum for all five new support towers is

    sum_(S subset L,|S|>=3) product_(p in S)gp=17/2100.

Deleting them afterward by this cap sum, using the same B, gives only

    5+B/(s_base-17/2100)=11.643739975212638...,

which exceeds566/49. Integrating them into their actual normalized17 and19 rows gives HG1 instead. Thus the retained extension is not justified by simply charging the new towers against the old scalar reserve. This compares sufficient estimates and does not exclude other old certificates for particular instances.

For a narrower subclass omitting{11,13,17}, the original Report570 schedule with t19=6 already gives11.547534092653025..., with nine-prime Haar lower bound>1/500000. For ALL five supports that same fixed schedule gives11.589961619419185..., which fails its sufficient gate. The final theorem changes only t19 to7; no maximal-support or optimal-schedule claim is made.

## 5. Relation to the existing terrain

Report561 covers arbitrary rooted supports but lacks these nonrooted high supports. Report563 permits all mixed supports on L under a root-prefix condition and excludes the E9 pairs involving5 or7; that condition is not assumed here. Report572 permits broad supports through a distinct shallow-selector/actual-fibre premise, which is not imposed or inferred here. The new class admits arbitrary root phases within its star/triangle supports and arbitrary phases/heights on all five added towers. The missing non3 pair{11,13}, other omitted pairs, and arbitrary rooted higher supports remain outside HG1.

Evidence: [late_hypergraph_joint_source.py](../../frontier/cover-geometry/late_hypergraph_joint_source.py) and [exact data](../../frontier/cover-geometry/late_hypergraph_joint_source.json). Running python3 -I -S -B -O passes47 named exact checks, including reproduction of Report570's baseline, the exact new charges, low probability/mean checks, the same-law continuation algebra, the two fixed comparison schedules, the failed a-posteriori cap certificate, and literal numerical cofactor inventory uniqueness. The general theorem follows from the ordinary derivation above; finite arithmetic does not establish its arbitrary-family quantifiers. No new Lean verification is claimed.
