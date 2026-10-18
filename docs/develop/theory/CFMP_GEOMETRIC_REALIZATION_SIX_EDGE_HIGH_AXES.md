# CFMP six-edge high-axis expenses and the remaining owner count

Sections 1–355 refer to the preceding theory, ending with
[the five-reservoir return and six-edge source continuation](CFMP_GEOMETRIC_REALIZATION_FIVE_RESERVOIR_RETURN.md).
The section numbering continues that theory.

The two M/U expense implications below are repo-derived from the
published paired response formulas and original-normal-circle framework.
Their hypotheses differ: the V/C branch uses actual D degree at least
six; the V/D branch uses no degree bound beyond whatever is needed to
supply its explicitly stated one-sided gap. The exact finite polynomial
certificates are displayed in full. These are mathematical arguments,
not claims of Lean or kernel verification.

The final sections identify an honest remaining owner-count obligation.
No full six-edge flat exclusion or general geometric realization theorem
is asserted.

## 356. M/U axes with transverse V/C: hypotheses and conclusion

Retain the six-label setting of Sections 341 and 348: exactly M,V,C,D,Z,U; one fixed four-distinct-label paired frame per original owner; one actual connected circular normal link per label; original nonnegative angles summing to 2π; unique flat sigma=(M,C,D,V,C,D); every other owner genuine; genuine tau=(Z,M,C,D,M,C). Write shared coshes as m,v,c,d,z,u. Assume

    c,d,v>1, m>1+c+d, 1<v≤m−2,
    z>1+m+c, u>m,
    (m−1)(v−1)≥(c+d)²,
    z<u+m+1.

The last inequality is an explicit one-sided upper-gap premise.
Sections 318–321 supply it when their hypotheses hold: a finite actual
paired quotient, four distinct labels in each fixed frame, connected
normal circles of degree at least six, complete original angle sums
2π, and a wholly genuine star at a largest actual cosh. Here Z and U
have wholly genuine stars and all remaining values are at most m;
applying that result to the larger gives |z−u|<m+1.

Independently of how the gap is supplied, the actual D-link degree is
required to be at least six for this V/C implication. No degree lower
bound at another edge is used directly.

**Theorem 356.1 (repo-derived).** Every genuine eta=(M,V,C,U,V,C), up to exchanging axes or transverse labels within its fixed frame, has theta_M(eta)+theta_U(eta)>π.

The proof first excludes every actual opposite-M owner (W,M,D,C,M,D) and every actual opposite-V owner (W,V,D,C,V,D) under a bad eta. It then uses the actual D circle and its degree. It assumes no receiver inventory.

## 357. Response formulas and the actual budgets

For axes r,o and transverse values a,b, put

    L=(a+b)²−(r−1)(o−1), J=(r+1)(o+1)−(a−b)²,
    D_a,b(x)=x²+a²+b²+2xab−1,
    N_a=b(r+o)+a(ro+b²−a²+1).

Genuine responses have L,J>0,

    tan²(theta_r/2)=(r−1)J/((r+1)L),
    cos(beta_a)=N_a/sqrt(D_a,b(r)D_a,b(o)).

When a>b, with t=sqrt(L/J),

    beta_a=atan(A_+ t)+atan(A_− t),
    A_±=(sqrt(a²−1)±sqrt(b²−1))/(a+b)>0.

Equivalently, as a function of an axial angle theta_r,

    beta_a(theta_r)=atan(lambda_+ cot(theta_r/2))
                    +atan(lambda_− cot(theta_r/2)),
    lambda_±=A_± sqrt((r−1)/(r+1)).

This response is strictly decreasing in theta_r. At theta_r=π/2 it lies in (0,π/2), with tangent

    T(a,b,r)=sqrt((a²−1)(r²−1))/(a+rb).             (357.1)

T is strictly increasing in a and r and decreasing in b, for all a,b,r>1. Its angle lies below π/2 because lambda_+lambda_−<1.

Sigma leaves total genuine capacities π at M and V, and 2π at D. Original slots remain separate under any self-gluing. Suppose for contradiction that a genuine eta has

    theta_M(eta)+theta_U(eta)≤π.                    (357.2)

Tau and eta are distinct, so their actual M slots obey

    2 beta_M(tau)+theta_M(eta)≤π.                  (357.3)

Flatness and v≤m−2 imply

    c+d<m−2, c,d<m−3, m>4.                        (357.4)

The axial eta cosine, with denominator

    E=m²+v²+c²+2mvc−1,

has numerator 2vc+m(v²+c²)−(m²−1)u. It increases with v,c and decreases with u on 1<v,c≤m−2,u≥m. The v derivative's numerator is

    2(m²−1)[−c³+cmu+cv²+c+mv+vu]>0,

and the c formula is symmetric. At v=c=m−2,u=m, E−2N=(m+1)(7m−9)>0. Therefore

    theta_M(eta)>π/3, beta_M(tau)<π/3.             (357.5)

These are actual eta and tau slots.

## 358. A common upper-axis bound and c<5m/12

Let p=sqrt((m−1)(u−1)) and q=sqrt((m+1)(u+1)). The positive half-angle product from (357.2) gives

    pq≤v²+c²+2vc(q−p)/(q+p)≤v²+c²+2vc/m.         (358.1)

The last step uses u>m and (q−p)/(q+p)≤1/m. Since pq>(m−1)(u−1),

    u<U=1+[v²+c²+2vc/m]/(m−1).

The upper gap and v≤m−2 therefore give

    z<R(m,c):=m+2+[(m−2)²+c²+2c(m−2)/m]/(m−1).  (358.2)

Write

    D_t(x)=x²+m²+c²+2xmc−1,
    N_t(z,d)=c(z+d)+m(zd+c²−m²+1),
    C_t(z,d)=N_t(z,d)/sqrt(D_t(z)D_t(d)).

C_t strictly increases in z and d for m>c>1. For example the sign numerator of its z derivative is

    (m²−1)[c(dz+m²−c²+1)+m(d+z)]>0.              (358.3)

Set d1=m−c−1. If c≥5m/12, compare tau to z=R,d=d1. The exact polynomial

    Q_C(m,c)=m²(m−1)²[D_t(R)D_t(d1)−4N_t(R,d1)²]

is positive throughout m>4,5m/12≤c<m−2. The full finite positivity certificate is specified in Section 364. Hence |C_t(R,d1)|<1/2, while the actual tau cosine is strictly smaller. This contradicts (357.5). Thus

    1<c<5m/12<4m/9.                               (358.4)

R increases with c, and the exact identity

    9m/4−R(m,4m/9)=(17m²−45m−72)/(324(m−1))>0

holds for m>4; the numerator at m=4+b is 17b²+91b+20. Consequently

    v,z,u<9m/4.                                   (358.5)

## 359. Every opposite-M owner is impossible

Suppose an actual kappa has axes w,c and pair m,d. Its other axis label W is V,Z,or U, so w<9m/4 by (358.5). Its cosine is

    C=N/sqrt(D(w)D(c)),
    D(x)=x²+m²+d²+2xmd−1,
    N=d(w+c)+m(wc+d²−m²+1).

It increases with w since m>d. Increase w to r0=9m/4. There r0 c<m² by (358.4). The d derivative has sign numerator (m²−1)P, where

    P=(c+r0)d⁴+4m(cr0+1)d³+6m²(c+r0)d²
      +4m[cr0(m²−cr0)+m²+c²+r0²−1]d
      +(c+r0)[m⁴−c²r0²+c²+r0²−1]>0.

Thus increase d to d0=m−c−2, using (357.4). The polynomial

    Q_M(m,c)=16[D(r0)D(c)−4N²] at d=d0

is positive for m>4,1<c<4m/9 by the second certificate in Section 364. The comparison cosine has absolute value below 1/2, so the actual beta_M(kappa)>π/3.

Kappa and eta are distinct because kappa contains D and eta does not. Their original M slots cost

    2 beta_M(kappa)+theta_M(eta)>π,

contradicting the genuine M capacity. No opposite-M owner exists anywhere.

## 360. Additional two-owner bounds: m>16, v>4m/5, d>m/2, v>d

Because u>m, the left side of (358.1) is greater than m²−1. Using v≤m−2,c<5m/12 in its right side gives

    25m²−456m+480>0.

For 4<m≤16 this polynomial equals

    25(m−4)(m−16)+44m−1120<0.

Therefore m>16, in particular m>14.

Using the weaker c<4m/9 in (358.1) gives

    v²>65m²/81−8m/9+7/9>16m²/25.

The last difference, multiplied by 2025, is 329m²−1800m+1575; at m=14+b it equals 329b²+7412b+40859>0. Thus v>4m/5>c.

Also v>m−c. Otherwise the right side of (358.1) is at most its value at v=m−c, which is strictly below m²−1 because the difference is

    2c(m−c−1)+2c²/m−1>0.

Here m−c>3 by (357.4). Hence v>m−c>d+2, so in particular v>d.

Finally suppose d≤m/2. By (358.2), (358.3), and monotonicity in d, tau's M cosine is smaller than C_t(R,m/2). The polynomial

    Q_D(m,c)=4m²(m−1)²[D_t(R)D_t(m/2)−4N_t(R,m/2)²]

is positive on m>14,1<c<4m/9 by the third certificate. Thus this comparison cosine has absolute value below 1/2, again contradicting (357.5). We have proved

    m>16, v>4m/5, d>m/2, v>d, v>c.               (360.1)

## 361. Eta's two V slots each exceed π/4

Put t=sqrt(L_eta/J_eta). Equation (357.2) implies t²≥p/q>(m−1)/(m+1). Since v>c, both individual transverse-response coefficients A_± are positive. The eta V angle is therefore greater than its reference value at t0=sqrt((m−1)/(m+1)). This reference angle lies in (0,π/2) and has tangent

    T0=sqrt((v²−1)(m²−1))/(v+mc).

Monotonicity, v>4m/5 and c<4m/9 give

    T0>sqrt((16m²/25−1)(m²−1))/(4m/5+4m²/9)>1.

For the last inequality, multiply the difference of squared numerator and denominator by 2025. The result is

    896m⁴−1440m³−4617m²+2025.

At m=4+b this equals

    896b⁴+12896b³+64119b²+123320b+65369>0.

Consequently

    beta_V(eta)>π/4.                              (361.1)

## 362. Every opposite-V owner is impossible

Suppose an actual rho has axes w,c and transverse pair v,d, with W in {M,Z,U}. By (358.5), w<9m/4; by (358.4), c<4m/9; by (360.1), v>d. The transverse V cosine increases with either axis. For example, its w derivative has sign numerator

    (v²−1)[d(cw+v²−d²+1)+v(c+w)]>0.

Thus increase the axes independently to r0=9m/4,c0=4m/9, keeping v,d unchanged. These are comparisons of algebraic cosines with positive denominators; no virtual genuine owner is asserted.

For

    D(x)=x²+v²+d²+2xvd−1,
    N=d(r0+c0)+v(r0c0+d²−v²+1),

the polynomial

    Q_V(m,v,d)=1296[D(r0)D(c0)−2N²]

is positive on m>14,4m/5<v<m,m/2<d<v by the fourth certificate. Therefore the comparison cosine has absolute value below 1/sqrt(2). The actual beta_V(rho)>π/4.

Rho and eta are distinct because rho contains D and eta does not. Their four original V slots cost

    2 beta_V(rho)+2 beta_V(eta)>π,

contradicting the genuine V capacity. Thus no opposite-V owner exists anywhere.

## 363. Actual D-circle closure and its degree contradiction

Sigma is the unique CD-pair owner: every such genuine owner's shifted axial product would be at least (m−1)(v−1)≥(c+d)², contradicting its strict L>0. This uses z,u>m>v and four distinct labels.

As in Sections 345–346, a face with label set {X,C,D}, X=M or V, can have only transverse pair CD, XC, or XD. The possibilities are now exactly:

    MCD: sigma, or a D-axis MC owner; the MD alternative is excluded.
    VCD: sigma, or a D-axis VC owner; the VD alternative is excluded.

Select both original transverse D intervals of sigma, and every original axial D interval whose fixed transverse pair is MC or VC. Sigma intervals each have one MCD endpoint and one VCD endpoint; selected axial intervals have two MCD or two VCD endpoints, respectively. The displayed receiving classification proves that this nonempty set is closed under all actual face-endpoint identifications. Hence connectedness of the actual D circle forces it to contain every D interval. This is the original normal circle, including self-gluings and repeated visits, not a marked auxiliary graph.

Every genuine selected interval costs more than π/2:

* For a D-axis MC owner xi, its two actual M slots together with eta's axial M slot obey 2 beta_M(xi)+theta_M(eta)≤π. By (357.5), beta_M(xi)<π/3. At theta_D=π/2, the response (357.1) satisfies

      T(m,c,d)>sqrt((m²−1)(m²/4−1))/(m+5m²/24)>sqrt(3).

  The squared comparison, multiplied by 192, is

      23m⁴−240m³−816m²+192.

  At m=16+b this is 23b⁴+1232b³+22992b²+166400b+315584>0. Thus the reference angle is greater than π/3. Since the response decreases in theta_D, beta_M(xi)<π/3 forces theta_D(xi)>π/2.

* For a D-axis VC owner xi, (361.1) and the four actual V slots give beta_V(xi)<π/4. At theta_D=π/2,

      T(v,c,d)>sqrt((16m²/25−1)(m²/4−1))/(4m/5+5m²/24)>1.

  The squared comparison, multiplied by 14400, is

      1679m⁴−4800m³−22032m²+14400.

  At m=16+b this is 1679b⁴+102656b³+2326512b²+23117312b+84748352>0. The reference angle is greater than π/4, so theta_D(xi)>π/2.

The proof does not need to identify the other axial label of xi. Eta and xi are always distinct because xi contains D. The two subset budget arguments do not add their occurrences together or double-count eta in any one sum.

The actual D degree is at least six. Exactly two D intervals belong to sigma, each with zero angle. All remaining at least four intervals are genuine selected D-axis slots, each with angle greater than π/2. Their sum is therefore greater than 2π, contradicting the original D angle sum. This disproves (357.2) and proves the conclusion.

## 364. Complete finite polynomial certificates

The arrays below give every coefficient of the four polynomials defined here. Every nonzero coefficient is a positive integer and each constant coefficient is positive. The identities and signs are exact; no sampled inequality is used.

Write I_x[f; l,h](s)=(1+s)^n f((l+hs)/(1+s)), where n is the polynomial's degree in x and all other variables are unchanged. These are literal finite polynomial substitutions, with cancellation of the displayed denominator power.

1. C certificate:

       P_C(a,b)=12^6 I_c[Q_C;5m/12,m−2](a) at m=4+b.

   Q_C has c-degree 6. P_C has 76 positive integer coefficients, minimum 300524, and constant 3030471671808. For 5m/12≤c<m−2, the parameter a=(c−5m/12)/(m−2−c) is nonnegative; b=m−4>0.

2. Opposite-M certificate:

       P_M(a,b)=9^4 I_c[Q_M;1,4m/9](a) at m=4+b.

   Q_M has c-degree 4. P_M has 34 positive integer coefficients, minimum 89600, and constant 401533200. The actual domain has a,b>0.

3. D lower-bound certificate:

       P_D(a,b)=9^6 I_c[Q_D;1,4m/9](a) at m=14+b.

   Q_D has c-degree 6. P_D has 74 positive integer coefficients, minimum 1099008, and constant 52912522611541008. Its actual domain has a,b>0.

4. Opposite-V certificate:

       T_V(m,v,t)=I_d[Q_V;m/2,v](t),
       P_V(a,b,t)=10^6 I_v[T_V;4m/5,m](a) at m=14+b.

   Q_V has d-degree 4, and T_V has v-degree 6. P_V has 245 positive integer coefficients, minimum 212170752, and constant 2642912638787072. For 4m/5<v<m and m/2<d<v the parameters a=(v−4m/5)/(m−v), t=(d−m/2)/(v−d), and b=m−14 are positive.

All positive scaling factors and denominator powers have been stated. These identities therefore prove the indicated strict inequalities on the full continuous domains, not only on sampled values.

### Full coefficient arrays for Section 364
For P_C, P_M and P_D, a row i is the list of coefficients of
b^0,b^1,... in the coefficient of a^i. For P_V, a row (i,k)
is the analogous list in the coefficient of a^i*t^k. All unlisted
coefficients are zero. The tuple lengths are part of the complete
identities; omitted terminal coefficients are zero.

P_C:
```text
0 : (
  3030471671808,7505994711040,8255084658688,5294136006656,
  2183827082752,601809727232,111123170368,13344632504,
  963147430,34437998,300524
)
1 : (
  18813729374208,47682088992768,53907091857408,35769869469696,
  15412424755200,4501236152832,901399454304,122082404664,
  10691509872,546400200,12379248
)
2 : (
  48575835537408,125615960948736,145243377008640,98875702020096,
  43893048771072,13281879560832,2776414361760,396315793440,
  37023630624,2047510368,50992704
)
3 : (
  66767855026176,175709279158272,206853197783040,143465284270080,
  64938678870528,20057007079296,4284524761344,625717716480,
  59856655104,3390360192,86413824
)
4 : (
  51527796129792,137654613540864,164313719562240,115369710815232,
  52757664173568,16417945022976,3521346877440,513999240192,
  48854969856,2728733184,67931136
)
5 : (
  21169527717888,57270512222208,69035390705664,48759575463936,
  22309344497664,6894755997696,1453506342912,205539710976,
  18541965312,954021888,20901888
)
6 : (
  3617006026752,9885279191040,11983339044864,8454730088448,
  3825129111552,1150511579136,229956599808,29429858304,
  2185740288,71663616
)
```

P_M:
```text
0 : (
  401533200,705701160,490743117,168460236,
  28474740,1889568
)
1 : (
  1579188960,2832065856,2041319556,747862146,
  143961462,13291128,419904
)
2 : (
  2189103408,3945786048,2884905396,1087564644,
  220689846,22512168,881280
)
3 : (
  1246180032,2220521760,1616224320,612719298,
  126790938,13462632,567360
)
4 : (
  233118912,396413656,276297603,101044244,
  20369254,2130840,89600
)
```

P_D:
```text
0 : (
  52912522611541008,30867783517471680,7869274109913960,1145045992755168,
  104010863180949,6039342290808,218897359254,4527877320,
  40920957
)
1 : (
  571674852509510880,356008076871898464,98120540289186792,15702571137518568,
  1607218879045356,109044671447214,4900435766190,140528707434,
  2330664030,17006112
)
2 : (
  2320832310919505136,1516929430076928144,442351663542440748,75693635663694696,
  8403661146562704,631205573030640,32392762469451,1117140643314,
  24636837123,310938912,1679616
)
3 : (
  4514023838085091200,3048492820250616768,922117998697807968,164450427504824304,
  19139668761483900,1518126483267846,83051331014250,3091606474284,
  74865923460,1063523520,6718464
)
4 : (
  4460475737555940528,3079760925047385744,954246895923218004,174702043590560928,
  20925505311554790,1713144034936926,97064668494594,3757393677060,
  95079233619,1419768000,9497088
)
5 : (
  2118545630001864000,1484957854885497696,467536071987095112,87069756338253360,
  10620984286900062,886666384602756,51300887871888,2031135639786,
  52662400830,807358752,5557248
)
6 : (
  369998396795025600,261884045482921680,83302044127465884,15681257619376704,
  1934615949472635,163443465015666,9576117878469,384203782338,
  10101947469,157181472,1099008
)
```

P_V:
```text
(0,0) : (
  2642912638787072,1057186813829888,175212032060480,15397141637760,
  756463208880,19694055168,212170752
)
(0,1) : (
  13483791747742208,5490284285868032,927548159006720,83226639248640,
  4183138660320,111668113152,1236860928
)
(0,2) : (
  23900367337091328,9865279827443712,1690507741336320,153957067943040,
  7860216535920,213326687232,2404712448
)
(0,3) : (
  17168073153920000,7171177989248000,1243542687737600,114614905113600,
  5923016313600,162749721600,1857945600
)
(0,4) : (
  4007814368480000,1695750641312000,297640523134400,27750504038400,
  1449981158400,40268390400,464486400
)
(1,0) : (
  23334606272599040,9411632018844160,1575423708489600,140084339699200,
  6978147197600,184625933760,2026736640
)
(1,1) : (
  117503018187847680,48030178158520320,8154168882355200,736000626182400,
  37252229443200,1002521257920,11207393280
)
(1,2) : (
  207907032382809600,85914397271270400,14750626035225600,1346971309785600,
  69004087341600,1880502048000,21300019200
)
(1,3) : (
  150262411245440000,62694801559936000,10868184175603200,1002083082515200,
  51838924395200,1426739731200,16323379200
)
(1,4) : (
  35599859031360000,15002480385984000,2625433764700800,244273483468800,
  12746885068800,353786572800,4080844800
)
(2,0) : (
  79478453892032000,32205675570208000,5420749604568000,485112598288000,
  24344806058000,649569816000,7199280000
)
(2,1) : (
  400226426307289600,163969725254451200,27917506195200000,2528572399616000,
  128499863356000,3474176846400,39041740800
)
(2,2) : (
  712020579803206400,294440590845721600,50613134179180800,4629490480604800,
  237663630078800,6493174358400,73762099200
)
(2,3) : (
  518903498181120000,216359258588928000,37499463981753600,3458542204089600,
  179038702689600,4932904377600,56518041600
)
(2,4) : (
  124112847125280000,52173198491232000,9113274306638400,846796911782400,
  44151910502400,1224950054400,14129510400
)
(3,0) : (
  137127715618048000,55718149836160000,9408731186080000,845174280960000,
  42596489880000,1142083152000,12726720000
)
(3,1) : (
  696021606434816000,285550548347904000,48703345037056000,4420555516736000,
  225204255616000,6105888720000,68833152000
)
(3,2) : (
  1251106672154240000,517602574639360000,89043294779136000,8153500028416000,
  419152758776000,11470545216000,130553856000
)
(3,3) : (
  921137989241600000,383906137655040000,66532632427648000,6137601841088000,
  317887220848000,8765235648000,100528128000
)
(3,4) : (
  221805747030400000,93081392709760000,16238011167712000,1507454330112000,
  78553746432000,2178807552000,25132032000
)
(4,0) : (
  127993486852160000,52084010114080000,8810797271640000,793118158000000,
  40068598850000,1077205680000,12039840000
)
(4,1) : (
  658830942970560000,270501313608960000,46183291680000000,4197036249120000,
  214130264100000,5815374480000,65681280000
)
(4,2) : (
  1201461688618080000,497196345112320000,85575307883040000,7841520027120000,
  403482221610000,11053838880000,125971200000
)
(4,3) : (
  895395159152000000,373067804636800000,64651425113760000,5965157406400000,
  309077278640000,8527308480000,97873920000
)
(4,4) : (
  216696324468000000,90824680783200000,15829520033640000,1468558258560000,
  76494867840000,2121281280000,24468480000
)
(5,0) : (
  61672109456000000,25108386318400000,4250258862000000,382906523200000,
  19363290500000,521141400000,5832000000
)
(5,1) : (
  323783012281600000,132974661344000000,22712796720000000,2065269312800000,
  105442956400000,2865994200000,32400000000
)
(5,2) : (
  601457793560000000,248926338640000000,42855919478400000,3928695851200000,
  202264483700000,5545130400000,63244800000
)
(5,3) : (
  454686726000000000,189407290800000000,32823144120000000,3028952124000000,
  156991181400000,4333327200000,49766400000
)
(5,4) : (
  110474387400000000,46260079320000000,8056778106000000,747076780800000,
  38901600000000,1078617600000,12441600000
)
(6,0) : (
  12018328904000000,4890760364000000,827559257000000,74528142000000,
  3767571750000,101367000000,1134000000
)
(6,1) : (
  64761479640000000,26591923456000000,4541582240000000,412953752000000,
  21084224500000,573129000000,6480000000
)
(6,2) : (
  123083866100000000,50938953520000000,8770508124000000,804163198000000,
  41413310750000,1135782000000,12960000000
)
(6,3) : (
  94620396000000000,39409988800000000,6829528940000000,630322532000000,
  32678329000000,902340000000,10368000000
)
(6,4) : (
  23063007500000000,9650322500000000,1679788175000000,155698920000000,
  8105472000000,224712000000,2592000000
)
```

## 365. M/U axes with transverse V/D: hypotheses and conclusion

Consider a finite face-paired tetrahedral quotient with exactly six actual
edge labels M,V,C,D,Z,U. Each original owner has one fixed vertex-induced
paired frame, in edge order (12,13,14,34,24,23),

    (R,A,B,O,A,B),

where all four displayed labels are distinct. Face maps preserve actual
labels. Every actual edge has a connected circular normal link. Original
edge occurrences, including repeated visits, are distinct intervals and
angle slots. Loops, repeated role vectors and distinct-face self-gluings
are allowed. Shared positive cosh lengths are m,v,c,d,z,u. All original
angles are nonnegative and sum to 2*pi at every actual edge.

The unique flat owner is sigma=(M,C,D,V,C,D), with angles pi at M,V
and zero at its transverse C,D slots. Every other owner is genuine, and
there is a genuine tau=(Z,M,C,D,M,C). Assume

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    z<u+m+1.                                            (365.1)

The last inequality is an explicit one-sided upper gap. The complete-star maximum-gap theorem in Sections 318–321 supplies
it under the original hypotheses recalled in Section 356. No degree bound is otherwise needed for this implication.

**Theorem 365.1 (repo-derived).** Every genuine owner eta with axes M,U and transverse
pair V,D satisfies

    theta_M(eta)+theta_U(eta)>pi.                         (365.2)

This is an expense implication, not a claim that eta exists, a source-face
receiver inventory, or a complete six-edge flat-exclusion theorem.

## 366. Angles, original budgets and a bad eta

For a genuine paired response with axes r,o and transverse values a,b,

    L=(a+b)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(a-b)^2>0,
    D_a,b(t)=t^2+a^2+b^2+2*t*a*b-1,
    cos(theta_r)=[2*a*b+r*(a^2+b^2)-(r^2-1)*o]/D_a,b(r),
    cos(beta_a)=[b*(r+o)+a*(r*o+b^2-a^2+1)]
                  /sqrt(D_a,b(r)*D_a,b(o)).               (366.1)

Also tan(theta_r/2)^2=(r-1)*J/[(r+1)*L]. All actual genuine
angles lie in (0,pi). These are the original fixed-frame angles.

The complete genuine capacities at M,V,D are pi,pi,2*pi. Suppose
eta=(M,V,D,U,V,D) violates (365.2). Tau and eta are distinct, so

    theta_M(eta)+theta_U(eta)<=pi,
    2*beta_M(tau)+theta_M(eta)<=pi.                       (366.2)

Flatness and v<=m-2 give

    c+d<m-2, c,d<m-3, m>4.                              (366.3)

Write Q=v^2+d^2, T=v*d, and
p=sqrt((m-1)*(u-1)), q=sqrt((m+1)*(u+1)). The bad-axis condition
is equivalent to

    p*q<=Q+2*T*(q-p)/(q+p),
    Le/Je>=p/q>(m-1)/(m+1),                             (366.4)

where Le=(v+d)^2-(m-1)*(u-1) and Je=(m+1)*(u+1)-(v-d)^2.
Since 0<(q-p)/(q+p)<=1/m, 2*T<=Q, and u>m,

    p*q=sqrt((m^2-1)*(u^2-1))>u*(m^2-1)/m.

Consequently

    u<Q/(m-1), Q>m*(m-1),
    z<Q/(m-1)+m+1.                                     (366.5)

The weaker bound

    u<Zb(m,v,d):=1+[v^2+d^2+2*v*d/m]/(m-1)              (366.6)

will be convenient for two polynomial comparisons.

From Q<(m-2)^2+(m-3)^2 follows m^2-9*m+13>0. Together
with m>4 this gives m>43/6. Indeed on 4<m<=43/6,

    m^2-9*m+13=(m-4)*(m-43/6)+(13*m-94)/6<0.

We also have

    d^2>3*m-4, v^2>5*m-9.                               (366.7)

The eta M cosine has numerator and denominator

    Ne=2*v*d+m*(v^2+d^2)-(m^2-1)*u,
    De=m^2+v^2+d^2+2*m*v*d-1.

It increases in v,d and decreases in u on 1<v,d<m and u>=m.
For example its v derivative has sign numerator

    Ne_v*De-Ne*De_v
      =2*(m^2-1)*[-d^3+d*m*u+d*v^2+d+m*v+v*u]>0.

At v=d=m-2,u=m, De-2*Ne=(m+1)*(7*m-9)>0. Hence

    theta_M(eta)>pi/3, beta_M(tau)<pi/3.                 (366.8)

The comparison is algebraic, with positive denominators; no comparison
endpoint is claimed to be a genuine owner.

## 367. A stronger affine bound for the source companion

We claim

    c<3*m/7-3/2.                                        (367.1)

Suppose otherwise. Then d<m-c-2<=4*m/7-1/2. Increasing the
eta v,d variables to m-2,4*m/7-1/2 and decreasing u to m raises
its cosine. At that endpoint,

    De-3*Ne=(32*m^3+1828*m^2-1659*m-539)/196>0.

For m=7+b its coefficients are

    8*b^3/49+625*b^2/49+4091*b/28+451,

so positivity holds for m>7. Thus theta_M(eta)>acos(1/3).
The actual partial M budget then gives

    cos(beta_M(tau))>1/sqrt(3).                          (367.2)

For tau define

    Dt(t)=t^2+m^2+c^2+2*t*m*c-1,
    Nt(z,d)=c*(z+d)+m*(z*d+c^2-m^2+1),
    Ct(z,d)=Nt(z,d)/sqrt(Dt(z)*Dt(d)).

Ct increases strictly in z,d when m>c and z,d>1. For instance,

    Nt_z*Dt(z)-Nt*(z+m*c)
      =(m^2-1)*[c*(d*z+m^2-c^2+1)+m*(d+z)]>0.

Set d0=m-c-2 and R(m,c)=Zb(m,m-2,d0)+m+1. Equations
(365.1), (366.3), and (366.6) imply d<d0 and z<R. Thus
Ct(z,d)<Ct(R,d0). Define the polynomial

    A(m,c)=m^2*(m-1)^2*[Dt(R)*Dt(d0)-3*Nt(R,d0)^2].       (367.3)

It has degree six in c. If A=sum A_j(m)*c^j, the identity

    PA(a,b)=14^6*sum_{j=0}^6 A_j(m)
                *[3*m/7-3/2+(m-3)*a]^j*(1+a)^(6-j),
    m=7+b,                                              (367.4)

has the 76 positive integer coefficients displayed in Section 374.
It parametrizes c in [3*m/7-3/2,m-3), with a>=0, b>0.
Therefore A>0 and |Ct(R,d0)|<1/sqrt(3), contradicting (367.2).
This proves (367.1). This derivation used tau and eta only, not a receiver.

## 368. Every opposite-M exit is globally impossible

Suppose any actual owner has fixed frame

    kappa=(W,M,D,C,M,D), W in {V,Z,U}.                    (368.1)

It is genuine. Let r denote its W cosh. From (366.3), (366.6), and the
upper gap, every possible r is below R(m,c). In particular v<m<R,
u<Zb(m,m-2,d0)<R, and z<R. Also c<3*m/7.

We have c*R<m^2. To verify this explicitly, R equals

    [c^2*m-2*c*m^2+2*c*m+4*c+3*m^3-5*m^2-2*m+8]
      /[m*(m-1)].

The derivative of c*R has numerator

    3*m*c^2-(4*m^2-4*m-8)*c+3*m^3-5*m^2-2*m+8.

For 1<c<3*m/7,m>4 it is bounded below by
(9*m^3-23*m^2+10*m+56)/7>0. At c=3*m/7,

    m^2-c*R=(m^3+266*m^2+42*m-1176)/[343*(m-1)]>0.

For kappa put

    D(t)=t^2+m^2+d^2+2*t*m*d-1,
    N=d*(r+c)+m*(r*c+d^2-m^2+1).

Its M cosine is N/sqrt(D(r)*D(c)). The r derivative has sign

    (m^2-1)*[d*(c*r+m^2-d^2+1)+m*(c+r)]>0.

At r=R, its d derivative has sign (m^2-1)*P, where

    P=(c+r)*d^4+4*m*(c*r+1)*d^3+6*m^2*(c+r)*d^2
      +4*m*[c*r*(m^2-c*r)+m^2+c^2+r^2-1]*d
      +(c+r)*[m^4-c^2*r^2+c^2+r^2-1]>0.

The positivity uses c*r<m^2. Hence increasing r to R and then d
to d0 strictly raises the M cosine. Define

    B(m,c)=m^2*(m-1)^2*[D(R)*D(c)-4*N(R,c,d0)^2]          (368.2)

with d=d0 in D. It has degree six in c. For B=sum B_j(m)*c^j,

    PB(a,b)=7^6*sum_{j=0}^6 B_j(m)
                *[1+(3*m/7)*a]^j*(1+a)^(6-j), m=4+b,    (368.3)

has the 76 positive integer coefficients in Section 374. This covers
1<=c<3*m/7, b>0, and proves B>0. The comparison cosine therefore
has absolute value less than 1/2. Thus beta_M(kappa)>pi/3.

Kappa and eta are distinct: kappa contains C and eta does not. Their
actual original M slots cost

    2*beta_M(kappa)+theta_M(eta)>pi,

contradicting the complete genuine M capacity. This excludes every
owner of type (368.1), whether or not it meets a source face.

## 369. Any opposite-V exit would force v<d

Suppose any actual owner has fixed frame

    rho=(W,V,D,C,V,D), W in {M,Z,U}.                      (369.1)

It is genuine and its W cosh r satisfies
r<Q/(m-1)+m+1 by (366.5). The actual four V slots at rho and eta
have budget 2*beta_V(rho)+2*beta_V(eta)<=pi. Define

    Lr=(v+d)^2-(r-1)*(c-1),
    Jr=(r+1)*(c+1)-(v-d)^2,
    K=[sqrt(v^2-1)+sqrt(d^2-1)]/(v+d),
    x=K*sqrt(Lr/Jr), y=K*sqrt(Le/Je).

Their transverse sums are S(rho)=2*atan(x), S(eta)=2*atan(y).
By (366.7),

    K^2>(3*m-5)/(3*m-4),
    y^2>K^2*(m-1)/(m+1).                                (369.2)

For lambda>1 put Ac=(1+lambda)*c+lambda-1. Exact expansion and
2*T<=Q give

    Lr-lambda*Jr
      >[2-Ac/(m-1)]*Q-Ac*(m+1)-(lambda-1)*c-lambda-1.   (369.3)

For lambda=3/2 or 4/3, (367.1) makes the coefficient of Q positive.
Use Q>m*(m-1) and substitute the upper bound c0=3*m/7-3/2.
The right side of (369.3) is strictly greater than, respectively,

    (-2*m^2+45*m+21)/14,   (67*m+28)/21.                 (369.4)

If 43/6<m<=10, the first is positive. Thus

    x^2*y^2>(3/2)*(33/35)^2*(37/49)
             =120879/120050>1.

If m>=10, the second is positive and

    x^2*y^2>(4/3)*(25/26)^2*(9/11)
             =1875/1859>1.

Therefore xy>1 and S(rho)+S(eta)>pi. For a response with pair V,D,

    beta_V=atan(K*t)+atan(B*t),
    beta_D=atan(K*t)-atan(B*t),
    B=[sqrt(v^2-1)-sqrt(d^2-1)]/(v+d), t=sqrt(L/J).

If v>=d, then B>=0 and beta_V>=S/2 at both owners. Their actual
V expense would exceed pi. Hence every rho as in (369.1) forces

    v<d.                                                (369.5)

## 370. Sharper low-label bounds and two tangent bounds

By flatness and (369.5),

    F(c,d):=(c+d)^2-(m-1)*(d-1)<0.

The identity

    F=[c+d-(m-1)/2]^2+(m-1)*[c+1-(m-1)/4]

gives c<(m-5)/4 and m>9. Now Q<2*d^2 and Q>m*(m-1)
imply d>2*m/3. We claim

    c<3*m/20-1, m>40/3.                                 (370.1)

If c>=3*m/20-1, monotonicity of F in c and in d on d>=2*m/3
would give

    F(c,d)>F(3*m/20-1,2*m/3)=m*(m+120)/3600>0,

a contradiction. This proves (370.1).

Take lambda=5 in (369.3). Its Q coefficient is positive under (370.1).
After Q>m*(m-1) and c<3*m/20-1, the right side is greater than

    m*(2*m+5)/10>0.

Thus Lr>5*Jr. From m>40/3 and (369.2),

    x^2>5*(35/36)=175/36>(11/5)^2,
    y^2>(35/36)*(37/43)=1295/1548>(10/11)^2.             (370.2)

In particular x>11/5 and y>10/11.

## 371. The source D tangent exceeds sqrt(2)

Let

    w=tan(theta_D(tau)/2)
      =sqrt((d-1)*Jt/[(d+1)*Lt]), t=sqrt(Lt/Jt),
    Lt=(m+c)^2-(z-1)*(d-1), Jt=(z+1)*(d+1)-(m-c)^2.

The source M angle is

    beta_M(tau)=atan(A_+*t)+atan(A_-*t),
    A_+/-=[sqrt(m^2-1)+/-sqrt(c^2-1)]/(m+c)>0.

This is strictly increasing in t. If w<=sqrt(2), then

    t>=t0=sqrt((d-1)/[2*(d+1)]).

At t0 the arctangent sum is below pi/2, since
A_+*A_-*t0^2=(m-c)/(m+c)*t0^2<1. Its tangent exceeds sqrt(3)
exactly when

    P(m,c,d)=8*(m^2-1)*(d^2-1)
                 -3*[(m+3*c)*d+3*m+c]^2>0.              (371.1)

This holds on (370.1), d>2*m/3. The expression decreases in c,
so replace c by c2=3*m/20-1. As a quadratic in d, its leading
coefficient is

    (677*m^2+10440*m-14000)/400>0.

At d=2*m/3 its d derivative is

    (1354*m^3+4437*m^2+11240*m-10800)/600>0.

Therefore it increases beyond that endpoint. Its endpoint value is

    (2*m+1)*(1354*m^3-12683*m^2-11160*m+18000)/3600.

Writing m=40/3+b, this equals

    677*b^4/900+90311*b^3/2700+5679151*b^2/10800
      +8073593*b/2430+4616045/729>0.

Thus (371.1) holds. The source M angle would be greater than pi/3,
contradicting (366.8). Hence

    w>sqrt(2).                                          (371.2)

## 372. Every opposite-V exit is globally impossible

By (370.2), xy>2 and the increasing function (xy-1)/(x+y) satisfies

    (xy-1)/(x+y)>55/171>sqrt(3)-sqrt(2)
                          >sqrt(1+w^2)-w.               (372.1)

For the middle inequality, sqrt(3)>19/11 and sqrt(2)>7/5 give
sqrt(3)+sqrt(2)>172/55>171/55; take reciprocals. The last uses
(371.2) and strict decrease of sqrt(1+w^2)-w.

Since xy>1, atan(x)+atan(y)-pi/2 belongs to (0,pi/2). The other
comparison angle pi/4-atan(w)/2 also belongs to (0,pi/2). Their
tangents are the left and final expressions in (372.1). Therefore

    2*atan(w)+4*atan(x)+4*atan(y)>3*pi,

or equivalently

    theta_D(tau)+2*S(rho)+2*S(eta)>3*pi.                  (372.2)

The actual owners tau,rho,eta are distinct: tau has no V, and rho
has C while eta does not. The charge in (372.2) is tau's one D-axis
slot, rho's two V and two D slots, and eta's two V and two D slots.
Their complete genuine V/D capacity is pi+2*pi. This contradiction
excludes every owner of type (369.1), globally. No rho existence premise
was used until its actual existence was supposed for contradiction.

## 373. Original-face transitions and actual D-circle closure

Sigma is the only owner whose fixed transverse pair is CD. Indeed the
two distinct axes of such an owner lie in {M,V,Z,U}; since z,u>m>v,
the smallest shifted axial product is (m-1)*(v-1)>=(c+d)^2.
Its genuine L test therefore fails, and the unique-flat premise forces
it to be sigma.

The four original faces of (R,A,B,O,A,B) have label sets

    F4=123: {R,A,B}, F3=124: {R,A,B},
    F2=134: {O,A,B}, F1=234: {O,A,B}.

A face with labels X,C,D, where X=M or V, has fixed transverse pair
CD, XC or XD. Pair CD forces sigma. Pair XD would be an owner globally
excluded in Sections 368 and 372. Pair XC has an axial D interval. Therefore
its original D corner belongs precisely to sigma or to an axial D
interval with fixed pair MC or VC. Every such face has one D corner,
and every label-preserving face map sends it to the receiving D corner.

In the actual D normal circle, select both original transverse D intervals
of sigma (edges 14 and 23) and every axial D interval of every owner with
fixed pair MC or VC. Each sigma interval has one endpoint on an MCD face
and one on a VCD face. Each selected MC-pair axial interval has both
endpoints on MCD faces; each VC-pair axial interval has both on VCD faces.
The complete classification above makes this nonempty set endpoint-closed.
It is consequently a union of complete connected components of the actual
D-link graph. Connectedness makes it the whole actual D circle.

Eta, however, has two original transverse D intervals with companion V
and axes M,U. It is not sigma and its D intervals are not axial. They
lie outside the selected set, a contradiction. This proves (365.2).

All selections were by original intervals and face incidences. Repeated
owners along the circle, equal role vectors, loops and face self-gluings
do not merge angle slots or alter endpoint closure. No source-face
partner count was assumed. The explicit upper gap was used in (366.5),
(367.3) and the ensuing opposite-exit bounds; it is not inferred from bare
connectedness. No full six-edge flat exclusion follows from this theorem.

## 374. Complete finite coefficient identities

In each row below, row j lists the coefficients of b^0,b^1,...,b^10
in the coefficient of a^j. Thus the rows specify the entire polynomial,
including the displayed zero entries. All other entries are positive
integers. PA is exactly (367.4), and PB is exactly (368.3).
```text
P_A
0 : (748892015808496,1060818919929258,670310799943309,248618355834380,59884669387501,9776554693052,1093913379076,82670151200,4027442432,113770752,1406976)
1 : (7930540440464096,12018878349094624,8182119967889980,3295012858560612,869263689270956,156970862930812,19649200985176,1683527329568,94482291456,3136141568,46749696)
2 : (24038653285352440,36809929127254640,25303115392945096,10280633406069768,2733703801694628,497021759403680,62562776281124,5382775360032,302898211840,10064578048,149925888)
3 : (34151224342374720,52311045165734880,35942851942791584,14584982770243984,3869706364358576,701270467811760,87881088355312,7517496612192,419941847808,13827828224,203714560)
4 : (25478185201943040,38861784243481920,26561424464234016,10707745797157024,2818016919445952,505578259675552,62574884665440,5270935967808,288860045824,9286837504,132765696)
5 : (9615809414002176,14524858795442688,9808928517322368,3895536416197888,1006098690304064,176242913338240,21154710055360,1712242301952,89003418112,2663304448,34420736)
6 : (1421034691862016,2100915108762624,1380180709547136,528688945341312,130107483208640,21327019184128,2327929233728,163119867904,6656109824,120472576,0)

P_B
0 : (45741931200,153489591360,223475804937,185128466334,96199587267,32565713796,7198354065,1004487162,80471916,2823576,0)
1 : (263197620000,882232371720,1288768827360,1077054073620,568813956704,197842793764,45732149526,6891777578,639203824,31966914,605052)
2 : (623825899200,2081522075640,3036823028722,2544400896688,1353504457305,477138220790,112779344622,17619503202,1734227894,96260892,2247336)
3 : (780820840800,2585967181560,3754146763528,3138523314192,1671140533748,591925700758,141282248800,22445795148,2270456944,131718174,3309264)
4 : (544453249200,1785015578640,2570124961572,2135179922148,1132080037613,400202643512,95600834168,15257882444,1558774378,92060220,2383164)
5 : (200232060000,648129754720,922471540270,758418612126,398361835284,139647070276,33115807228,5254592112,534959516,31602858,823032)
6 : (30218941200,96252512360,134859429677,109159336018,56431252801,19454932070,4531910481,705423012,70372870,4071816,103932)
```

## 375. Scope of the resulting global owner-count reduction

Combine Theorems 341.2 and 348.2 with Theorems 356.1 and 365.1.
The following reduction is in the low-sixth, six-actual-edge,
four-distinct-fixed-frame source normal form. It does not assert
complete flat exclusion.

Retain exactly six actual labels M,V,C,D,Z,U, the unique flat
sigma=(M,C,D,V,C,D), genuine tau=(Z,M,C,D,M,C), original connected
circles of degree at least six and full angle sums 2*pi. All other
owners are genuine. The scalar conditions are

    c,d,v>1, m>1+c+d, v<=m-2, z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    u<z+m+1 and z<u+m+1.

The two gaps come from the complete-star maximum-gap theorem in
Sections 318–321 with all its original hypotheses, recalled in Section
356. The M/Z implication uses the first, and the
new M/U implications use the second; neither gap is discarded.

Put P={M,Z,U} and L={V,C,D}. An owner's P expense is the sum of all
its original slots labelled in P, with the two transverse repetitions
counted separately. The complete genuine P capacity is 5*pi.

## 376. Every owner with at least two P labels costs more than pi

There are three exhaustive role classes.

1. Both axes lie in P and both transverse labels lie in L. Pair CD is
   impossible for a genuine owner, since sigma is the unique CD-pair
   owner. Pair VC or VD is covered by the M/Z, Z/U or M/U expense
   implication. These two axial slots alone cost more than pi.

2. A P label p is transverse and a different P label r is axial,
   while the other transverse value q is in L. Then p,r>=m and
   1<q<=m-2. At least one of p,r is strictly greater than m. In the
   response

       beta_p=atan(A*t)+atan(B*t), t=cot(theta_r/2),
       A,B=[sqrt(p^2-1)+/-sqrt(q^2-1)]/(p+q)
                               *sqrt((r-1)/(r+1)),

   A,B>0 and

       A+B=2*sqrt(p^2-1)/(p+q)*sqrt((r-1)/(r+1))>1.

   The comparison value p=r=m,q=m-2 is exactly one; the expression
   increases strictly in p,r and decreases in q. If A*B*t^2>=1,
   beta_p>=pi/2>atan(t). Otherwise its tangent is
   (A+B)*t/(1-A*B*t^2)>t. Thus theta_r+2*beta_p>pi.
   Additional P slots only add nonnegative expense.

3. Both transverse labels p,q lie in P. If an axis r also lies in P,
   put K=[sqrt(p^2-1)+sqrt(q^2-1)]/(p+q) and
   lambda=K*sqrt((r-1)/(r+1))>(m-1)/m>1/2. The transverse sum is
   S=2*atan(lambda*cot(theta_r/2)). For t>0 and lambda>1/2,
   2*atan(lambda*t)>atan(t): if lambda^2*t^2>=1 this is immediate;
   otherwise compare tangents using 2*lambda>1. Therefore
   theta_r+2*S>pi. If neither axis is in P, their values r,o are at
   most m-2. The strict genuine tests then give

       L>(2*m)^2-(m-3)^2, J<=(m-1)^2,
       L/J>3, K^2>1-1/m^2.

   Hence K^2*L/J>1, S=2*atan(K*sqrt(L/J))>pi/2, and the four
   transverse P slots cost 2*S>pi.

All cases use original slots and distinct actual owners. Thus the number
of genuine owners containing at least two P labels is at most four.

## 377. Some one-P owners are also expensive

A four-distinct owner with exactly one P label uses that label and all
three labels V,C,D. If its pair is PC, its axes are V,D. For the
transverse P cosine, as a function of its V-axis value r,

    N(r)=c*(r+d)+p*(r*d+c^2-p^2+1)

has positive slope c+p*d. At r0=1+p+c,

    N(r0)=[c+p*(1+p+c)]*(1+c+d-p)<0,

because p>=m>1+c+d. Actual v<=m-2<r0 therefore gives beta_P>pi/2.
Its two P slots already cost more than pi. Interchanging C,D handles
pair PD. These owners are genuine whenever they occur; their fixed
frames are never changed by this comparison.

Consequently the union of the following actual-owner classes has at
most four members:

- owners with at least two P labels;
- owners with exactly one P label and transverse pair PC or PD.

The claim follows by summing their separate strict P expenses against
5*pi. This does not count the unique flat sigma as a genuine owner.

## 378. At least two genuine owners remain outside those classes

Every genuine paired owner has total angle less than 2*pi. Indeed,
with transverse sum S=2*atan(K*sqrt(L/J)) and K<1, each axial angle
obeys

    tan(theta_r/2)*tan(S/2)=K*sqrt((r-1)/(r+1))<1.

Both angles belong to (0,pi), so theta_r+S<pi. Apply this to both
axes and add. The unique flat sigma has total angle exactly 2*pi.

If there are N actual owners, the six complete edge sums give total
angle 12*pi. Therefore 12*pi<2*N*pi, so N>=7. There are at least
six genuine owners. Section 377 accounts for at most four of them.

Each of the remaining at least two owners has exactly one P label,
because four distinct labels cannot all lie in the three-element L.
Its pair cannot be CD (the unique owner of that pair is sigma), PC
or PD. Thus it has one of exactly these forms, up to exchanging the
axes or the two transverse positions within its fixed frame:

    (P,V,C,D,V,C),
    (P,V,D,C,V,D),
    (C,P,V,D,P,V),   P in {M,Z,U}.                      (378.1)

Every such owner has V transverse. They are distinct actual owners;
repeated copies of the same role still count separately.

This is the residual obstruction to the proposed global sum. Proving
that all two-P owners cost more than pi does not eliminate (378.1).
Further actual-circle or joint-angle work is needed to rule out the
required collection of at least two such owners.

## 379. Exact scalar witness to the blanket-expense shortcut's failure

A scalar example makes the missing inference concrete. Use

    (m,v,c,d,z,u)=(50,47,6,41,74,80),
    sigma=(M,C,D,V,C,D),
    tau=(Z,M,C,D,M,C), rho=(U,V,D,C,V,D).

All source scalar orders, the source flat product and both maximum
gaps hold: (m-1)*(v-1)=2254>2209=(c+d)^2 and |z-u|=6<51.
The two owners are genuine, with

    (Lt,Jt)=(216,1214), (Lr,Jr)=(7349,531).

For tau the transverse M,C cosine numerators are 29240 and 38744.
For rho the transverse V,D cosine numerators are 1317 and 45411.
All are strictly positive, so all four transverse angles are acute.
Every partial label budget is strictly respected:

- M and V each have two acute slots, costing less than pi;
- C has two acute tau slots plus one genuine rho axis, less than 2*pi;
- D has one genuine tau axis plus two acute rho slots, less than 2*pi;
- Z and U each have one genuine axis, less than pi.

Rho contains just one P label, U, and its P expense is its one genuine
U-axis angle, strictly less than pi. Thus the scalar orders, gaps,
flat product and this full set of partial budgets do not imply that
every genuine owner spends more than pi on P.

This is not an actual face quotient, a completed angle-equation system,
a degree-six realization, or a counterexample to six-edge flat exclusion.
It is an exact counterexample only to that blanket scalar expense claim.
No source-face partner existence or complete-circle realization is asserted.

## 380. A joint budget for the transverse P/V residual family

Keep the source inequalities

    p>=m>1+c+d, v>1, c,d>1,
    (m-1)(v-1)>=(c+d)^2,

and let a genuine owner have axes C,D and transverse labels P,V,
where the actual label P is one of M,Z,U, with shared cosh p.
Assume p>v, as supplied by v<=m-2 in the low-sixth source normal form.
The four labels remain distinct actual labels even when some numerical
coshes of other labels agree. No incidence or receiver hypothesis is used.

Write beta_P,beta_V for its original transverse angles. Then

    2 beta_P > 2 arctan(2) > 2*pi/3,
    2 beta_P + 2 beta_V > 4 arctan(2) > 4*pi/3.

The repeated factors of two count the four original transverse slots.

**Proof.**

Set s=p+v, h=c+d and

    L=s^2-(c-1)(d-1), J=(c+1)(d+1)-(p-v)^2.

Genuineness supplies L,J>0. Source flatness and p>=m give

    h^2 <= (p-1)(v-1) <= (s-2)^2/4.

Thus h<=(s-2)/2, and h>2 gives s>6. By the elementary product
bounds at fixed sum,

    (c-1)(d-1) <= (h-2)^2/4 <= (s-6)^2/16,
    (c+1)(d+1) <= (h+2)^2/4 <= (s+2)^2/16.

Consequently

    L/J >= (15*s^2+12*s-36)/(s+2)^2 > 9,

since the numerator minus 9*(s+2)^2 is 6*(s-6)*(s+2)>0.
Also

    K=[sqrt(p^2-1)+sqrt(v^2-1)]/s
      > (s-2)/s > 2/3.

The standard genuine paired response therefore yields

    S:=beta_P+beta_V=2 arctan(K sqrt(L/J))>2 arctan(2).

Since p>v, the other paired-response identity gives

    beta_P-beta_V
       =2 arctan([sqrt(p^2-1)-sqrt(v^2-1)]/s * sqrt(L/J))>0.

Thus beta_P>S/2>arctan(2). The displayed slot expenses follow.
Finally arctan(2)>pi/3 because 2>sqrt(3).

### Actual-budget consequences and the open boundary

In the six-edge unique-flat source setting the genuine M capacity is pi,
the genuine V capacity is pi, and the genuine Z and U capacities are
2*pi each. The theorem implies:

- At most one transverse M/V owner with axes C,D occurs.
- At most two transverse Z/V owners with axes C,D occur, and likewise
  at most two transverse U/V owners.
- At most four owners in the union of these three transverse P/V
  classes occur: each spends more than 4*pi/3 on P union {V}, whose
  complete genuine capacity is 6*pi.

These are separate valid subset sums of original slots, not simultaneous
additions that double-count a slot. They do not classify the remaining
axial-P/transverse-V,C or axial-P/transverse-V,D owners, and do not prove
flat exclusion. These bounds do not resolve the required collection of at least two
residual owners in Section 378. The full six-edge flat-exclusion
obligation remains open.

## 381. Exact boundary of the universal joint H-expense shortcut

Let P={M,Z,U} and H={M,Z,U,V}. In the six-edge unique-flat source
normal form, the complete genuine H capacity would be 6*pi. The
following exact example shows that the source scalar conditions,
both maximum gaps, genuine tests and all source-front partial budgets
do not imply that each genuine owner spends more than pi on H.

Take

    (m,v,c,d,z,u)=(52,38,2,40,70,80),
    sigma=(M,C,D,V,C,D),
    tau=(Z,M,C,D,M,C), rho=(U,V,D,C,V,D).

All six labels are distinct actual labels. Their displayed coshes are
also distinct here. The source inequalities hold:

    m=52>1+c+d=43, 1<v=38<=m-2=50,
    z=70>1+m+c=55, u=80>m,
    (m-1)*(v-1)=1887>1764=(c+d)^2,
    |z-u|=10<m+1=53.

For the strict paired tests L=(a+b)^2-(r-1)*(o-1) and
J=(r+1)*(o+1)-(a-b)^2, the two genuine owners have

    (Ltau,Jtau)=(225,411), (Lrho,Jrho)=(6005,239).

Their transverse cosine numerators are

    tau: N_M=5472, N_C=16722,
    rho: N_V=15326, N_D=3316.

They are all strictly positive, so all four transverse angles are acute.
The partial source-front budgets, including sigma, are therefore strict:
M and V each retain two acute genuine slots costing less than pi;
C has two acute tau slots plus one genuine rho axis, less than 2*pi;
D has one genuine tau axis plus two acute rho slots, less than 2*pi;
Z and U each have one genuine axis, less than pi.

Nevertheless rho spends less than pi on H. Its only H slots are its
one U axis and its two V transverse occurrences. Write theta_U and
beta_V for their angles. In the standard response formulas,

    Drho(u)=252643, Drho(c)=9127,
    A_U=233762, N_V=15326,
    cos(theta_U)=A_U/Drho(u),
    cos(beta_V)=N_V/sqrt(Drho(u)*Drho(c)).

The exact integer comparison is

    2*N_V^2-Drho(c)*(Drho(u)-A_U)
      =2*15326^2-9127*18881
      =297445665>0.

Hence cos(beta_V)^2>sin(theta_U/2)^2. Since cos(beta_V)>0
and theta_U/2 lies in (0,pi/2), this gives

    beta_V < (pi-theta_U)/2,
    theta_U+2*beta_V < pi.

The example does not prescribe any face pairing, complete the edge
angle equations or realize a degree-six quotient. It is not a
counterexample to six-edge flat exclusion. It refutes only the proposed
per-owner H expense from these scalar and partial-budget premises.
A complete-star or joint collection argument remains necessary.

## 382. Complete hypotheses and precise scope

Consider a finite face-paired tetrahedral quotient with exactly six
actual edge labels M,V,C,D,Z,U. Each original tetrahedron owner has one
fixed vertex-induced paired frame, in edge order (12,13,14,34,24,23),

    (R,A,B,O,A,B),

with four distinct actual labels R,A,B,O. Face maps preserve actual
labels. Every actual normal link is one connected circle of original
degree at least six. Loops, repeated role vectors, repeated visits and
distinct-face self-gluings are allowed in these hypotheses. Original
edge occurrences remain distinct angle slots and link intervals.

There is one shared positive generalized length at each actual label;
write its cosh as m,v,c,d,z,u. Original angles are nonnegative and sum
to 2*pi at each actual edge. The unique flat owner is

    sigma=(M,C,D,V,C,D),

with axial M,V angles pi and transverse C,D angles zero. Every other
owner is genuine, with all its angles in (0,pi), and an actual genuine
source owner

    tau=(Z,M,C,D,M,C)

exists. Assume

    c,d,v>1, m>1+c+d, 1<v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    u<z+m+1 and z<u+m+1.                              (382.1)

The two gaps are retained explicitly. Under the stated complete-star
hypotheses they are supplied by Sections 318–321 of the preceding
continuation: the larger of Z,U has a wholly genuine star, the two
largest other values are the smaller of z,u and m, and the theorem
requires the connected degree-at-least-six circle, complete angle
sum and fixed four-distinct frames. Neither gap follows from bare
connectedness. The M/Z expense uses u<z+m+1; the M/U expenses use
z<u+m+1. The M/U V/C branch separately uses actual D degree at least
six. These dependencies are not weakened here.

The genuine paired tests and angle responses are those of the fixed
frames. For axes r,o and pair a,b,

    L=(a+b)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(a-b)^2>0.

**Theorem 382.1 (restricted low-V exclusion, repo-derived).**
No quotient satisfying these hypotheses can also satisfy

    v<=c and v<=d.                                    (382.2)

Thus a surviving low-sixth, unique-flat normal form must have
v>min(c,d). This closes only the region (382.2), not the full six-edge
flat-exclusion problem.

## 383. A strict opposite-axis ordering lemma

**Lemma 383.1 (repo-derived).** Let a,b,v>1 and p>=m>1. Suppose

    (m-1)*(v-1)>=(a+b)^2

and an owner with axes p,b and transverse pair v,a is genuine. Then
v>b.

Indeed p>=m and v-1>0 give

    (p-1)*(v-1)>=(a+b)^2.

Its strict L test gives (v+a)^2>(p-1)*(b-1). Multiply by v-1>0:

    (v+a)^2*(v-1) > (a+b)^2*(b-1).                   (383.1)

The right side is f(b) for f(x)=(x+a)^2*(x-1). On x>1,

    f'(x)=(x+a)*(3*x+a-2)>0.

Thus (383.1) is f(v)>f(b), forcing v>b. The proof does not require
numerical inequality between a and b, or between any other distinct
labels. In particular v=b is excluded by the strict genuine test.
No face partner, circle degree, gap, or partial budget is used in this
scalar lemma.

Apply it with p in {m,z,u}. An axial-P residual owner of the form
(P,V,C,D,V,C) requires v>d; an owner of the form (P,V,D,C,V,D)
requires v>c. Consequently both families are absent under (382.2).

## 384. Every genuine owner then spends more than pi on H

Put P={M,Z,U} and H={M,Z,U,V}. An expense is the sum of the owner's
original slots with labels in the specified set; two transverse
occurrences are always counted separately.

We use Theorems 341.2 and 348.2 from the preceding continuation
and the implications of Sections 356–380 above, with exactly
the hypotheses retained here. The role classification is exhaustive:

1. Every genuine owner containing at least two P labels has P expense
   greater than pi (Section 376). This covers all placements of those
   labels, including three-H/one-low placements. Its H expense is at
   least its P expense and is therefore greater than pi.

2. A genuine owner with exactly one P label uses that label and all
   three labels V,C,D, because its frame has four distinct labels.
   If its fixed pair is PC or PD, its two P slots cost more than pi
   (Section 377), so its H expense again exceeds pi.

3. Its fixed pair cannot be CD: the two distinct axes would belong
   to {M,V,Z,U}, with shifted product at least
   (m-1)*(v-1)>=(c+d)^2. Its strict genuine L test would fail.
   The unique owner of that pair is the flat sigma.

4. If its pair is VC or VD, its axes are P and the other low label.
   Section 383 excludes both possibilities under (382.2).

5. The only remaining pair is PV, with axes C,D. Section 380 gives

       H expense = 2*beta_P+2*beta_V
                 > 4*arctan(2) > 4*pi/3 > pi.

There is no zero-P owner, since only three labels lie outside P.
The cases cover actual labels, not numerical cosh values, so equal
lengths at distinct labels do not merge classes or lose an owner.
They do not infer that any particular receiving owner exists.

## 385. At least six genuine owners and the strict H contradiction

For completeness, the total-angle count of Section 378 applies here.
For any genuine owner with axes r,o and pair a,b, put

    K=[sqrt(a^2-1)+sqrt(b^2-1)]/(a+b),
    S=beta_a+beta_b=2*arctan(K*sqrt(L/J)).

We have 0<K<1 and S in (0,pi). The paired half-angle identity gives

    tan(theta_r/2)*tan(S/2)=K*sqrt((r-1)/(r+1))<1.

Both half angles lie in (0,pi/2), so theta_r+S<pi. Apply this to
both axes and add: every genuine owner's total six-slot angle is
strictly less than 2*pi. Sigma has total angle exactly 2*pi.

If there are N original owners, the six complete actual edge equations
sum to 12*pi. There is at least one genuine owner, namely tau, so

    12*pi < 2*N*pi.

Thus N>=7 and the number G=N-1 of genuine owners is at least six.

The complete H capacity is 8*pi. Sigma uses exactly 2*pi on H,
one pi at M and one at V. Hence the genuine H capacity is exactly
6*pi. But Section 384 gives a strict H expense greater than pi for
every one of the G genuine owners. Summing disjoint original slots,

    6*pi = sum_genuine H_expense > G*pi >= 6*pi,

a contradiction. Strictness still holds when G is exactly six.
This proves the theorem.

No pairing inventory, auxiliary-circle replacement or quotient-existence
claim enters the proof. In the remaining region v>min(c,d), this argument does not eliminate
one or both axial-P residual families from Section 378, depending on
the strict opposite-axis orders in Lemma 383.1. Full six-edge flat
exclusion remains open.

## 386. A weaker actual-incidence theorem for the source VCD faces

The low-V exclusion of Sections 382–385 also follows from a local
incidence argument with fewer hypotheses. The result below derives
actual receiving owners; it does not assume an inventory of them.

Consider a finite tetrahedral face pairing with exactly six distinct
actual edge labels M,V,C,D,Z,U. Each original owner has a fixed
vertex-induced paired frame (R,A,B,O,A,B), in edge order
(12,13,14,34,24,23), with four distinct actual labels. Each original
face is paired to a distinct other original face occurrence by a
label-preserving vertex map. Distinct-face self-gluings, loops and
repeated role vectors are allowed. A face paired to itself is outside
this convention. Distinct labels may have equal numerical coshes.

There is a distinguished flat owner

    sigma=(M,C,D,V,C,D).

Every other owner is genuine. For axes r,o and pair a,b its strict
genuine tests are L=(a+b)^2-(r-1)*(o-1)>0 and
J=(r+1)*(o+1)-(a-b)^2>0. Assume only

    z,u>=m>v>1, c,d>1,
    (m-1)*(v-1)>=(c+d)^2.                            (386.1)

The actual V normal link is the quotient of the original local V-edge
intervals by the endpoint identifications induced by the face pairing.
Assume that this quotient is one connected circle and has original
degree at least two. Here original degree counts original intervals,
not graph valence; no intervals are collapsed when roles repeat.

**Theorem 386.1 (actual VCD receiver ordering).** Each original VCD
face of sigma pairs to a face of an external genuine owner of type

    A(P)=(P,V,C,D,V,C), necessarily v>d; or
    B(P)=(P,V,D,C,V,D), necessarily v>c,
    P in {M,Z,U}.                                    (386.2)

The displayed forms permit exchanging the axes or transverse positions
within the same fixed frame. The two target face occurrences are
distinct, but their receiving owners need not be distinct.

Consequently v>min(c,d). If v<=d, both source faces use the B family;
if v<=c, both use the A family. The theorem assumes no tau owner,
upper gap, angle equation, high-axis expense inequality, or normal-circle
condition at another label. In particular degree six is not needed.
Only the strict L test of the genuine receivers will enter its proof.

## 387. Exhaustive fixed-pair alternatives at a VCD face

Any owner with fixed transverse pair CD has two distinct axes selected
from {M,V,Z,U}. Their shifted product is at least
(m-1)*(v-1)>=(c+d)^2 by (386.1), so its L test is nonpositive.
Every owner other than sigma is genuine. Hence sigma is the unique
actual owner with pair CD, even among repeated copies of its role.

Every original face of a fixed paired frame contains the two transverse
labels and one axis. A face with label set VCD therefore has exactly
one of these three alternatives:

- pair CD, whose owner is sigma;
- pair VC, with D axial and the other axis P in {M,Z,U};
- pair VD, with C axial and the other axis P in {M,Z,U}.

The latter two are exactly A(P) and B(P), and are genuine. These are
alternatives for original face occurrences, not just numerical edge
lengths. Equality of coshes at distinct labels changes none of them.

## 388. The source self-gluing and its original normal interval

Sigma's original V edge is 34. Its incident faces 134 and 234 are
exactly its two VCD faces; its other faces have label set MCD. Since
M and V are distinct actual labels, a VCD face cannot pair to an MCD
face. Thus an internal partner for either VCD face would have to be
the other VCD face of sigma.

The three edge labels of each face are distinct. There is exactly one
label-preserving vertex map between these two source faces:

    134 -> 234: 1 -> 2, 3 -> 4, 4 -> 3.              (388.1)

It reverses the endpoints 3 and 4 of the tetrahedron's V edge. No
orientation-preserving self-gluing is silently imposed. If the ambient
quotient convention excludes this reversal, the pairing is already
impossible. If it allows the reversal while satisfying the stated
original-normal-interval convention, the argument below still applies.

The tetrahedron-edge vertices 3 and 4 are different objects from the
two endpoints of its normal interval. The latter are the edge-in-face
incidences on faces 134 and 234. Under (388.1), these two normal
endpoints are paired with each other. Every original face has precisely
one partner, so each normal endpoint has precisely one paired endpoint.
There is no remaining endpoint through which another original interval
can attach. In particular recurring actual labels or quotient vertices
do not introduce further normal-endpoint identifications.

The one original V interval of sigma would therefore form a complete
connected component with its endpoints joined. This component is a
one-interval loop: its graph vertex has valence two, but its original
degree is one. Connectedness would make it the entire actual V normal
circle, contrary to original degree at least two. Thus neither source
VCD face pairs within sigma.

Both source faces have actual partners, so Section 387 forces each
partner to be an external A(P) or B(P) owner. This is the promised
existence deduction. It uses no count of distinct receiving owners.
If both partners belong to the same owner, its two different target
faces and two transverse V intervals remain separate original objects.
The argument is independent of a receiver's global orientation and
uses every compatible label-preserving local face map.

## 389. Strict receiver ordering and the surviving scope

Write either receiving owner with axes p,b and pair v,a, where
{a,b}={c,d} and p is one of m,z,u. Then p>=m. Put

    F=(p-1)*(v-1)-(a+b)^2 >= 0,
    L=(v+a)^2-(p-1)*(b-1) > 0,
    f(x)=(x+a)^2*(x-1).

The exact identity

    f(v)-f(b)=(v-1)*L+(b-1)*F>0                      (389.1)

retains strictness even when F=0. Since
f'(x)=(x+a)*(3*x+a-2)>0 for a,x>1, it follows that v>b.
For A(P) the opposite low axis is D, giving v>d; for B(P) it is C,
giving v>c. Numerical equality with that opposite label is excluded.
This proves Theorem 386.1.

In particular v<=c and v<=d is impossible under the weaker hypotheses
of Section 386. In the middle-V region, one family is forced at both
source faces, but the two partners may still be the same actual owner.
If v exceeds both c and d, either family remains possible. These
statements do not exclude those remaining regions, establish a complete
quotient there, or assert full six-edge flat exclusion.

## 390. A stronger charge for two transverse P labels

Retain the six-edge source-normal-form scalar conditions

    c,d,v>1, m>1+c+d, v<=m-2, z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    u<z+m+1, z<u+m+1.                              (390.1)

The labels M,V,C,D,Z,U are distinct actual labels; equal numerical
coshes at different labels are allowed. Every owner has its fixed
four-distinct paired frame (R,A,B,O,A,B), with edge order
(12,13,14,34,24,23). Put P={M,Z,U} and low={V,C,D}.

For a genuine owner with axes r,o and pair a,b, use its original slots
and the paired formulas

    L=(a+b)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(a-b)^2>0,
    K=(sqrt(a^2-1)+sqrt(b^2-1))/(a+b),
    S=beta_a+beta_b=2*atan(K*sqrt(L/J)),
    tan(theta_r/2)=sqrt((r-1)/(r+1))*sqrt(J/L).     (390.2)

Every genuine angle is in (0,pi). P expense counts each original
transverse occurrence twice and each axial occurrence once.

**Theorem 390.1.** Every genuine owner whose two transverse labels both
belong to P spends more than 4*pi/3 on P. Such an owner has either
four or five original P slots. The four-slot case needs no upper gap;
the five-slot case uses the two gaps exactly through

    each high value < the sum of the other two high values + 1.

**Corollary 390.2.** Also assume the unique flat source sigma has
frame (M,C,D,V,C,D), the genuine source tau has frame
(Z,M,C,D,M,C), and complete actual angle sums give genuine P capacity
5*pi. Then at most two genuine owners have both transverse labels in
P. The scalar theorem itself assumes no normal-circle topology.

The one-sided gaps in a full quotient are supplied only by the
complete-star maximum-gap theorem of published Sections 318–321 under
all its original hypotheses. This refinement does not assert either
gap from the remaining scalar conditions alone.

## 391. Source bounds and the full lower range of m

Every low value is at most m-2: this is explicit for v, while
c<m-d-1<m-2 and d<m-c-1<m-2. Every high value is at least m.
The source product and v<=m-2 imply

    (m-1)*(m-3)>4,

because c+d>2. Since m>3, this gives

    m>2+sqrt(5)>4.                                  (391.1)

For any transverse high pair p,q, both at least m,

    K>=sqrt(m^2-1)/m,                               (391.2)

because sqrt(x^2-1)/x increases for x>1, and K is the p,q-weighted
mean of this function. Also 0<K<1.

## 392. Four P slots: both axes low

If the axes r,o are both low and the pair p,q is high, then

    L>=4*m^2-(m-3)^2=3*(m+3)*(m-1),
    J<=(m-1)^2.

Thus, using J>0 and (391.2),

    K^2*L/J >= 3*(m+1)*(m+3)/m^2 > 3.

It follows that S>2*atan(sqrt(3))=2*pi/3. The four original
P slots have expense 2*S>4*pi/3. No gap is used here.

## 393. Five P slots: one axis high, one low

Write the high axis as r, the low axis as t, and the high pair as
p,q. These are exactly the three distinct high labels, so (390.1)
gives r<p+q+1. The exact branch requirements are:

- r=m: the inequality follows from z,u>=m>1, with no gap;
- r=z: it is exactly z<u+m+1;
- r=u: it is exactly u<z+m+1.

Thus no branch uses the opposite one-sided gap. We have t<=m-2
and p,q,r>=m.

The high axial angle is acute. Indeed, after exchanging p,q if needed,
p<=q, and

    r*t < (p+q+1)*(m-2)
        <=(p+q+1)*(p-2)
        < p^2+q^2.

The cosine numerator

    N_r=2*p*q+r*(p^2+q^2)-(r^2-1)*t
       =2*p*q+r*(p^2+q^2-r*t)+t

is positive. Hence theta:=theta_r<pi/2.

Put lambda=K*sqrt((r-1)/(r+1)). Then

    0<lambda<1, lambda>=(m-1)/m,
    E:=theta+2*S=theta+4*atan(lambda*cot(theta/2)). (393.1)

For fixed lambda>1/2 this last expression strictly decreases with
theta in (0,pi), since its derivative is

    1-2*lambda/[sin(theta/2)^2+lambda^2*cos(theta/2)^2]<0.

It strictly increases with lambda.

If m>=5, lambda>=4/5 and theta<pi/2, so

    E>pi/2+4*atan(4/5)>4*pi/3.                      (393.2)

For the last strict inequality,

    tan(2*atan(4/5))=40/9>2+sqrt(3)=tan(5*pi/12),

and both compared angles lie in (0,pi/2). Therefore
4*atan(4/5)>5*pi/6.

It remains to check 2+sqrt(5)<m<=5 without assuming m>=5.
The following exact comparison supplies the required sharper angle:

    cos(theta)>=2/(m+1)>=1/3.                       (393.3)

To prove it, raise t to m-2, then r to p+q+1. Along this path the
strict genuine interval is maintained: L remains positive because

    L>=(p+q)*(p+q-m+3)>0,

and J increases. Formula (390.2) shows theta increases with either t
or r while L,J remain positive. Its cosine therefore decreases.
At the final endpoint let N,D be the axial cosine numerator and
positive denominator, where D=r^2+p^2+q^2+2*r*p*q-1. Set
A=p-m>=0 and B=q-m>=0. Direct expansion gives

    (m+1)*N-2*D
      =(m+1)*(A^3+B^3)+(m-3)*(A^2*B+A*B^2)
       +(3*m^2+2*m-1)*(A^2+B^2)
       +(2*m^2-8*m-2)*A*B
       +(2*m^3-2*m)*(A+B) >= 0.                    (393.4)

Every coefficient is positive for m>2+sqrt(5); the constant is zero.
This proves (393.3), including all numerical high-label ties.

Now lambda>3/4 and theta<=theta0:=acos(1/3). The monotonicities in
(393.1), together with cot(theta0/2)=sqrt(2), give

    E>theta0+4*atan(3*sqrt(2)/4)>theta0+pi>4*pi/3,

because 3*sqrt(2)/4>1 and theta0>pi/3. This completes the five-slot
case, and hence the scalar theorem over the entire source range.

## 394. At most two double-P-pair owners

Tau has exactly three P slots: its Z axis and two transverse M slots.
The published mixed high-axis/transverse estimate in Section 376 gives

    theta_Z(tau)+2*beta_M(tau)>pi.

Tau's pair is MC, so it is distinct from every owner counted by this
refinement. If k actual genuine owners have both transverse labels in
P, their disjoint original P slots and tau's slots give

    5*pi >= P_expense(tau)+sum_{i=1}^k P_expense(i)
         > pi+k*(4*pi/3).

Thus k<3 and k<=2. Repeated copies of one role count as separate actual
owners; no bound on their multiplicity was assumed. Self-gluings do
not identify original angle slots or change this sum.

The only five-P-slot owners and the four-P-slot owners with both
transverse labels in P together have at most two members. The original
P-degree contributions remain five or four respectively, so repeated
role vectors cannot evade this count.

This does not cover the other four-P-slot class, whose two axes and
exactly one transverse label belong to P. It also does not eliminate
the cheap single-P axial families of Section 378 or prove full six-edge
flat exclusion. No general degree-weighted infeasibility claim is made.

## 395. The remaining four-P-slot class

Let

    m>3, r,p,o>=m, 1<q<=m-2,
    L=(p+q)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(p-q)^2>0.

For the paired frame (r,p,q,o,p,q), with edge order
(12,13,14,34,24,23), use the genuine angles determined by

    x=sqrt(L/J),
    theta_r/2=atan(sqrt((r-1)/(r+1))/x),
    theta_o/2=atan(sqrt((o-1)/(o+1))/x),
    beta_p=atan(Kplus*x)+atan(Kminus*x),
    Kplus=(sqrt(p^2-1)+sqrt(q^2-1))/(p+q),
    Kminus=(sqrt(p^2-1)-sqrt(q^2-1))/(p+q).

Every inverse tangent in these formulas is its ordinary real branch.
In particular theta_r,theta_o,beta_p are in (0,pi).

**Theorem 395.1.** The quantitative strict inequality is

    E:=theta_r+theta_o+2*beta_p
      >4*pi/3 + 3/(m+2) - 4/m^2
      >4*pi/3.                                             (395.1)

This theorem holds over the entire range m>3. It requires neither
high-label upper gaps nor the source-flat
condition, the special tau, or tau's angle budget. It does not claim the
stronger individual estimates theta_r+beta_p>2*pi/3 or
 theta_o+beta_p>2*pi/3. No coordinatewise monotonicity of E is used.

## 396. An elementary angle-distortion estimate

For u>3, put a=sqrt(1-u^(-2)). For phi in (0,pi), let psi be the unique
angle in (0,pi) whose positively oriented vector is proportional to

    (cos(phi), a*sin(phi)).

Then

    |psi-phi|<1/u^2.                                        (396.1)

Indeed, phi and psi are on the same side of pi/2, so their difference
has absolute value less than pi/2. If delta=|psi-phi|, the angle-between-
vectors formula gives

    tan(delta)=(1-a)*|sin(phi)*cos(phi)|
               /(cos(phi)^2+a*sin(phi)^2)
              <=(1-a)/(2*sqrt(a)).

The inequality follows by expanding
(|cos(phi)|-sqrt(a)*sin(phi))^2>=0; it also holds when the numerator is
zero. Using delta<=tan(delta), 1-a=1/(u^2*(1+a)), and a>1/2 gives

    delta<=1/(2*u^2*sqrt(a)*(1+a))<1/u^2.

This proves (396.1), including phi=pi/2.

## 397. Replacing the two axes by two positive scalars

Define

    z=sqrt((r+1)*(o+1)), y=sqrt((r-1)*(o-1)),
    h=(z+y)/2, k=(z-y)/2.

These letters z,y are local auxiliary scalars, not the named source
labels Z or V. The following bounds hold:

    h>=m, 1<=k<=h/m.                                        (397.1)

The first follows from z>=m+1 and y>=m-1. For the second,

    z^2-(y+2)^2
      =2*(sqrt(r-1)-sqrt(o-1))^2>=0,

so z>=y+2 and k>=1. Finally,

    y/z=sqrt((r-1)/(r+1))*sqrt((o-1)/(o+1))
       >=(m-1)/(m+1),

which rearranges to k/h<=1/m.

Set

    alpha=(theta_r+theta_o)/2, X=sqrt(L*J)>0,
    Np=p*(h^2+k^2+q^2-p^2)+2*q*h*k,
    Nh=h*(p^2+q^2+k^2-h^2)+2*k*p*q.

Because h+k=z and h-k=y, the original factors become

    L=(p+q)^2-(h-k)^2,
    J=(h+k)^2-(p-q)^2.                                     (397.2)

Both alpha and beta_p lie in (0,pi). The half-angle formulas yield

    cot(alpha)=Nh/(sqrt(h^2-1)*X),
    cot(beta_p)=Np/(sqrt(p^2-1)*X).                          (397.3)

For completeness, if a_r=sqrt((r-1)/(r+1)) and
 a_o=sqrt((o-1)/(o+1)), then

    a_r*a_o=(h-k)/(h+k),
    a_r+a_o=2*sqrt(h^2-1)/(h+k).

Consequently

    cot(alpha)=((h+k)*x^2-(h-k))/(2*sqrt(h^2-1)*x).

Substitution of (397.2) and x^2=L/J gives its expression in (397.3). Similarly,

    Kplus+Kminus=2*sqrt(p^2-1)/(p+q),
    Kplus*Kminus=(p-q)/(p+q),

and the tangent-addition formula gives the second expression in (397.3).
These cotangent identities remain valid at right angles, since their
positive sine denominators never vanish.

## 398. An exact comparison-angle sum

Define alpha0,beta0 in (0,pi) by

    cot(alpha0)=Nh/(h*X), cot(beta0)=Np/(p*X).

Equations (397.3) identify alpha as the angle-distortion of alpha0 with
u=h, and beta_p as that of beta0 with u=p. More explicitly, their
positively oriented vectors are respectively proportional to

    (cos(alpha0),sqrt(1-h^(-2))*sin(alpha0)),
    (cos(beta0),sqrt(1-p^(-2))*sin(beta0)).

Thus, by (396.1) and h,p>=m,

    E/2=alpha+beta_p>alpha0+beta0-2/m^2.                     (398.1)

Put T0=alpha0+beta0. Its range is (0,pi): initially it is in (0,2*pi),
and

    cot(alpha0)+cot(beta0)
      =[2*(q^2+k^2)+2*q*k*(p/h+h/p)]/X>0.

Since both individual sines are positive, this gives sin(T0)>0 and
hence the asserted range.

Three exact polynomial identities now give a simple cosine formula:

    Np^2+p^2*L*J
      =4*(h*k+p*q)*(h*p+k*q)*(h*q+k*p),
    Nh^2+h^2*L*J
      =4*(h*k+p*q)*(h*p+k*q)*(h*q+k*p),
    Np*Nh-p*h*L*J
      =-2*(h*k+p*q)*(h*q+k*p)*(h^2+p^2-q^2-k^2).

All factors in the first two right-hand sides are positive. Therefore

    cos(T0)=-(h^2+p^2-q^2-k^2)/(2*(h*p+k*q)).                (398.2)

The proof uses comparison angles defined by (397.3), not an assumption
that an actual Euclidean tetrahedron or quotient exists.

## 399. An exact bound on the comparison cosine

Let

    R=(m+5)/(m+2).

We claim that the scalar bounds (397.1), p>=m and q<=m-2 imply

    h^2+p^2-q^2-k^2>=R*(h*p+k*q).                           (399.1)

The function q^2+k^2+R*k*q increases in each positive variable q,k.
Thus the left side of (399.1) minus its right side is at least

    F=(1-1/m^2)*h^2+p^2-R*h*p
        -(m-2)^2-R*h*(m-2)/m.

Write A=h-m>=0 and B=p-m>=0. Exact expansion gives

    F=((m-1)*(m-3)/m)*A
        +(m*(m-1)/(m+2))*B
        +(1-1/m^2)*A^2+B^2-R*A*B.                          (399.2)

The constant term is zero. Since m>3, both displayed linear
coefficients are positive, 1-1/m^2>=8/9, and R<=8/5. Hence the
quadratic part is bounded below by

    (8/9)*(A^2+B^2)-(8/5)*A*B
      >=(4/45)*(A^2+B^2)>=0.

This proves (399.1), including boundary ties among r,p,o.

By (398.2), (399.1), and T0 in (0,pi),

    cos(T0)<=-(m+5)/(2*(m+2))<-1/2,

so T0>2*pi/3. The ordinary cosine is 1-Lipschitz on the real line;
therefore

    T0-2*pi/3
      >=cos(2*pi/3)-cos(T0)
      >=3/(2*(m+2)).                                      (399.3)

Combining (398.1) and (399.3) proves the first strict inequality in (395.1).
The remaining margin is positive because

    3/(m+2)-4/m^2
      =(3*m^2-4*m-8)/(m^2*(m+2))>0,
    3*m^2-4*m-8=3*(m-3)^2+14*(m-3)+7>0.

This completes the analytic derivation.

## 400. At most two owners have four or five P slots

In the six-label source application, every mixed four-P-slot owner
has axes r,o in P={M,Z,U}, high transverse label p in P, and low
transverse label q in {V,C,D}. The existing source inequalities give
r,p,o>=m, 1<q<=m-2 and m>2+sqrt(5)>3. Genuine owners have strict L,J>0.
Therefore the bound applies directly, with each original high slot
counted exactly once: E=theta_r+theta_o+2*beta_p.

Together with the double-P-pair refinement in Sections 390-394,
this covers every genuine owner having at least four P slots: the
four-slot double-P transverse class, the mixed four-slot class, and
the five-slot class. If tau is a distinct three-P-slot genuine owner
with P expense >pi and the total genuine P capacity is 5*pi, at most
two such four-or-five-slot owners can coexist with tau. Indeed k of
them would give total expense strictly greater than pi+k*(4*pi/3),
so k<3. Repeated roles are separate owners; original slots retain
their multiplicities.

The mixed four-slot branch needs no maximum gap. The union still
retains the five-slot branch requirements of Section 393: no gap for
high axis M, z<u+m+1 for high axis Z, and u<z+m+1 for high axis U.
Those gaps come from the complete-star theorem of Sections 318-321
only under all of that theorem's original hypotheses. This local
expense refinement alone is not a global six-edge exclusion.

## 401. Original degrees and the precise residual families

Work in the full six-actual-edge source setting of the published
continuation, with exactly six distinct actual labels

    P={M,Z,U}, Q={V,C,D}.

There are finitely many original tetrahedra, each with a fixed
vertex-induced paired frame (R,A,B,O,A,B), in edge order
(12,13,14,34,24,23), and four distinct actual labels. The unique flat
owner is sigma=(M,C,D,V,C,D); every other owner is genuine. The named
genuine source is tau=(Z,M,C,D,M,C). Every actual edge has a connected
original normal-circle quotient, original degree at least six, and
total angle 2*pi. Loops, self-gluings between distinct face occurrences,
repeated owners' role vectors, and equal numerical coshes at distinct
labels remain permitted.

The source scalar hypotheses are

    c,d,v>1, m>1+c+d, v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    u<z+m+1, z<u+m+1.

The last two gaps must either be hypotheses or follow from the
published complete-star maximum-gap theorem with its own hypotheses.
This proof does not infer them from the preceding scalar inequalities.
The full original degree/circle setting above is retained because the
older two-high-axis expense theorems, including the M/U V/C branch,
have those dependencies. The mixed-four-slot scalar theorem in
Sections 395-399 itself
uses no gap or degree hypothesis.

Call an owner cheap axial-P if its fixed frame, up to independently
interchanging axes and transverse labels, is one of

    A(P0)=(P0,V,C,D,V,C),
    B(P0)=(P0,V,D,C,V,D),       P0 in {M,Z,U}.

The word "cheap" names this residual role family. It does not assert
that every such owner actually spends less than pi. Let a be the number
of its genuine original owners, and f the number of genuine owners
having five original P slots. Then

    a+f>=3, f<=2, and a>=2.

In particular, if f=0 then a>=3. These are owner counts, not counts of
distinct role vectors, labels, face receivers, or normal-link vertices.
No full flat-exclusion conclusion is claimed.

## 402. The complete original-slot role table

Let n_P(T) be the number of original slots of a tetrahedron T whose
actual labels lie in P. An axial slot contributes one; a transverse
label contributes two. Every frame has at least one P label, since Q
has only three labels and the frame has four distinct labels.

There are 360 ordered fixed words: choose four distinct labels, then
order them in the four positions (R,A,B,O). The following is an
exhaustive partition. Interchanging the two axes or the two transverse
labels preserves the count and angle expense, but is not used to merge
original owners.

| P-label placement | Fixed words | n_P | Strict P-expense bound |
|---|---:|---:|---|
| One P axis, opposite V, transverse C,D | 12 | 1 | No genuine owner |
| One P axis, opposite C or D, transverse V and the other low label | 24 | 1 | >0; precisely A(P0), B(P0) |
| One transverse P label, paired with V, both axes C,D | 12 | 2 | >2*atan(2)>2*pi/3 |
| One transverse P label, paired with C or D, the other two lows axial | 24 | 2 | >pi |
| Two P labels, both axial, both transverse labels low | 36 | 2 | >pi |
| Two P labels, one axial and one transverse | 144 | 3 | >pi |
| Two P labels, both transverse, both axes low | 36 | 4 | >4*pi/3 |
| Three P labels, both axes high and one transverse label high | 36 | 4 | >4*pi/3 |
| Three P labels, both transverse labels high and one axis high | 36 | 5 | >4*pi/3 |

The entries sum to 360. Here "high" means a label in P and "low"
means a label in Q; numerical ties do not change the partition.

For a direct combinatorial check: a frame with one P label uses all
three low labels. Its 72 fixed words split into 36 with P axial and
36 with P transverse, with the subdivisions shown. A frame with two
P labels chooses its two high labels in three ways and its two low
labels in three ways. Each of the nine four-label sets has four words
with both P labels axial, sixteen with one axial and one transverse,
and four with both transverse, giving 36,144,36. A frame with three
P labels chooses its remaining low label in three ways. For each such
set there are twelve words with the low label axial and twelve with it
transverse, giving the final two classes of 36 words each.

## 403. Dependencies of every role charge

The first row is impossible by the published unique-C/D-pair theorem:
the transverse C,D pair occurs only at sigma. It is not a role deletion
based on a choice of face pairing or on a numerical search.

Rows four through six use the published P-expense classification in
Sections 376-377, including the separately established receiver-free
two-high-axis cases. In particular, row five does not silently assume
that a desired receiver exists. Row three uses the exact transverse
P/V lemma of Section 380.

Rows seven and nine use the double-P-pair refinement, Sections 390-394.
The four-slot case in row seven needs no maximum gap. The five-slot
case in row nine needs no gap when its high axis is M, needs
z<u+m+1 when its high axis is Z, and needs u<z+m+1 when its high axis
is U. These requirements are retained in the full hypotheses above.

Row eight uses Theorem 395.1:
for m>3, r,p,o>=m, 1<q<=m-2 and strict genuine factors L,J>0,

    theta_r+theta_o+2*beta_p
      >4*pi/3+3/(m+2)-4/m^2>4*pi/3.

The source hypotheses imply m>2+sqrt(5)>3, all P coshes are at least
m, and all Q coshes are at most m-2. Thus the theorem applies to each
owner of row eight, including ties among different labels' coshes.

These dependencies are mathematical premises of this counting
corollary. This file does not replace their proofs or narrow their
topological assumptions.

## 404. The genuine P degree and angle budgets

The three actual P edges have original degree at least six, so the
total original P degree is at least eighteen. The flat source sigma
has exactly one P slot, at its M axis. In the ordered label list
(M,Z,U), the componentwise genuine degree requirement is therefore

    genuine P degrees >= (5,6,6).

Tau contributes (2,1,0), so the genuine owners other than tau must
contribute at least (3,5,6), componentwise. These three requirements
remain separate; the following sum is only a necessary consequence:

    sum over genuine T of n_P(T) >= 17.                 (404.1)

The total angle on the three P edges is 6*pi. Sigma uses pi at M and
zero at Z,U, so the total genuine P expense is exactly

    sum over genuine T of expense_P(T) = 5*pi.         (404.2)

Both formulas count original incidences, even when owners repeat in
an actual edge circle. Neither formula replaces degree by graph
valence or counts a transverse label only once.

For every genuine owner, the role table gives the strict bound

    expense_P(T) > (pi/3)*(n_P(T)-I_f(T)-I_a(T)),       (404.3)

where I_f is one on a five-P-slot owner and zero otherwise, while I_a
is one on a cheap axial-P owner and zero otherwise. These two classes
are disjoint. For a cheap owner, (404.3) is the positivity of its genuine
axial angle. For a five-slot owner, its right side is 4*pi/3. For all
other rows, the displayed bound is at least the required n_P*pi/3,
with strictness as stated.

Summing (404.3), then applying (404.1) and (404.2), gives

    5*pi > (pi/3)*(17-f-a).

Thus f+a>2; since both are integer owner counts,

    f+a>=3.                                           (404.4)

## 405. At least two cheap axial-P owners

The source tau has three P slots, is not a five-slot owner, is not a
cheap axial-P owner, and has P expense greater than pi. Every owner
with at least four P slots has P expense greater than 4*pi/3 by rows
seven through nine. Hence there can be at most two such owners:
three of them together with tau would already spend more than 5*pi.
In particular,

    f<=2.                                             (405.1)

There are at least six genuine original owners. Indeed the six actual
edge angle sums total 12*pi, the unique flat sigma contributes 2*pi,
and every genuine paired tetrahedron has total six-slot angle strictly
less than 2*pi. Therefore the genuine count g satisfies

    10*pi < 2*pi*g, so g>=6.                           (405.2)

Suppose a<=1. Equations (404.4) and (405.1) force a=1 and f=2. By (405.2), besides
these three owners and tau, there are at least two further genuine
owners. Each is neither cheap axial-P nor five-slot. The role table
shows that every such genuine owner spends strictly more than
2*pi/3 on P. Counting only the two five-slot owners, tau, and these
two further owners gives

    total genuine P expense
      >2*(4*pi/3)+pi+2*(2*pi/3)=5*pi,

contradicting (404.2). Thus a>=2. Equation (404.4) also directly gives a>=3
when f=0.

## 406. Individual residual counts and the remaining boundary

This strengthens the former assertion that at least two owners lie
outside the expensive P classes: at least two must now be in the
specific axial residual families A(P0) or B(P0), rather than only in
the broader residual union that also includes transverse P/V owners.

The two forced owners are distinct original tetrahedra, but can have
the same role vector or high label. They need not both receive a
source VCD face, and the two source VCD faces may still have the same
receiver. The count asserts no new face-incidence pairing.

In subsequent budget arguments the six counts A(M),A(Z),A(U),B(M),
B(Z),B(U) must remain available separately. Their V,C,D costs and
their individual M,Z,U degree contributions need not be interchangeable.
The present integer count is not a complete joint budget or a
six-edge flat-exclusion theorem.

## 407. Standalone axial compensation

**Theorem 407.1.** Let r,v,a,b>1, and assume

    r>=max(v,a)+2,
    L=(v+a)^2-(r-1)*(b-1)>0,
    J=(r+1)*(b+1)-(v-a)^2>0.

For the genuine paired frame (r,v,a,b,v,a), write theta for the
axial angle at r and beta_v,beta_a for its transverse angles. If

    0<theta<=pi/3,

then

    3*theta+2*beta_v+2*beta_a>2*pi.                  (407.1)

Without the small-angle hypothesis, one always has

    4*theta+2*beta_v+2*beta_a>2*pi.                  (407.2)

The theorem uses no source-flat product, no source tau, no maximum
gap, no degree condition, and no normal-circle topology. It counts the
two original transverse slots of each label. Equal transverse coshes
are allowed. These are analytic statements about the paired response
formulas, without a Lean or kernel-verification claim.

## 408. Paired-angle reduction for compensation

Set

    x=sqrt(L/J), A=sqrt((r-1)/(r+1)),
    K=(sqrt(v^2-1)+sqrt(a^2-1))/(v+a),
    t=tan(theta/2)=A/x,
    lambda=A*K.

Then t>0, 0<lambda<1, and the transverse sum satisfies

    S:=beta_v+beta_a=2*atan(K*x)
      =2*atan(lambda/t)
      =pi-2*atan(t/lambda).                         (408.1)

All inverse tangents use their ordinary real branches. The hypothesis
theta<=pi/3 is exactly t<=1/sqrt(3).

We first establish the strict algebraic inequality

    2*lambda^2+t^2>1.                              (408.2)

## 409. The exact algebraic compensation

Put s=v+a, d=v-a and W=sqrt((v^2-1)*(a^2-1)). Temporarily vary the
opposite axial cosh b while keeping r,v,a fixed. The quotient

    J/L=[(r+1)*(b+1)-d^2]/[s^2-(r-1)*(b-1)]

strictly increases on 1<=b<=the given value. Its denominator is
positive throughout, and its derivative numerator is

    (r+1)*s^2+2*(r^2-1)-(r-1)*d^2
      =2*(v^2+a^2)+4*r*v*a+2*(r^2-1)>0.

This comparison does not require J to remain positive at b=1;
it is only a rational algebraic comparison with positive L. Since
the given b>1,

    t^2 > [(r-1)/(r+1)]*[2*(r+1)-d^2]/s^2.         (409.1)

The right side of (409.1) is permitted to be negative. Using

    K^2=(v^2+a^2-2+2*W)/s^2,

direct expansion gives

    2*lambda^2
      +[(r-1)/(r+1)]*[2*(r+1)-d^2]/s^2-1
      =2*[(r-1)^2-s^2+2*(r-1)*W]/[(r+1)*s^2].    (409.2)

The numerator on the right is strictly positive. By symmetry suppose
v>=a. Then r-1>=v+1 and W>=a^2-1. Therefore

    (r-1)^2-s^2+2*(r-1)*W
      >=(v+1)^2-(v+a)^2+2*(v+1)*(a^2-1)
      =(a-1)*(2*v*a+a+1)>0.                        (409.3)

Equations (409.1)-(409.3) prove (408.2), including v=a and the boundary
r=max(v,a)+2. No numerical approximation or monotonicity of an angle
in an unrelated coordinate enters this argument.

## 410. The conditional three-theta comparison

For 0<t<=1/sqrt(3), define

    lambda0=sqrt((1-t^2)/2).

Equation (408.2) gives lambda>lambda0, while lambda0>=t. We claim

    3*atan(t)>2*atan(t/lambda).                     (410.1)

If t=1/sqrt(3), the left side is pi/2, while lambda>lambda0=t
makes the right side strictly less than pi/2.

If 0<t<1/sqrt(3), both 3*atan(t) and 2*atan(t/lambda0)
lie in (0,pi/2). Their tangents are

    t*(3-t^2)/(1-3*t^2),
    4*t*lambda0/(1-3*t^2),

respectively. The first is larger, because both compared numerators
are positive and

    (3-t^2)^2-(4*lambda0)^2
      =(3-t^2)^2-8*(1-t^2)=(1+t^2)^2>0.

Thus 3*atan(t)>2*atan(t/lambda0)>2*atan(t/lambda), proving (410.1).
Combining (408.1) and (410.1) gives

    3*theta/2+S
      =3*atan(t)+pi-2*atan(t/lambda)>pi.

Multiplying by two proves (407.1).

## 411. The unconditional four-theta compensation

We prove (407.2) using the same strict algebraic inequality (408.2). If
theta>=pi/2, then 4*theta>=2*pi and S>0, so the result is immediate.
Otherwise 0<t<1. Put h=(1-t^2)/2, so 0<h<1. Equation (408.2) implies

    lambda>sqrt(h)>h=(1-t^2)/2.

Both theta=2*atan(t) and atan(t/lambda) lie in (0,pi/2), and

    tan(theta)=2*t/(1-t^2)>t/lambda.

Thus theta>atan(t/lambda). Using (408.1),

    2*theta+S=2*theta+pi-2*atan(t/lambda)>pi.

Multiplication by two proves (407.2). This proof is unconditional in the
axial angle; the stronger three-theta inequality (407.1) is still used only
when theta<=pi/3.

## 412. Source application and scalar scope

For a six-edge residual owner A(P0) or B(P0), let r be its high P0
cosh, v the V cosh, a its transverse C or D cosh, and b its opposite
low axial cosh. The source bounds give r>=m, v<=m-2 and a<m-2,
so r>=max(v,a)+2. Every such genuine owner with theta_P0<=pi/3
therefore obeys

    3*theta_P0+2*beta_V+2*beta_companion>2*pi.

Every such genuine owner, with no axial-angle restriction, obeys

    4*theta_P0+2*beta_V+2*beta_companion>2*pi.

The companion is C for A(P0), and D for B(P0). Its identity must be
retained in any joint budget. Only the three-theta estimate is
conditional on the small axial angle. These supply compensating low-label charges and do
not establish that every owner is expensive on H={M,Z,U,V}, that any
scalar inventory is a quotient, or by themselves exclude the full six-edge flat stratum.

The proof uses original slots and hence requires no simplification of
loops, self-gluings, repeated owners, or normal-link intervals.


## 413. Full hypotheses for the source-normal-form closure

The following deductions additionally assume the full six-edge source
setting. There are exactly six distinct actual labels M,V,C,D,Z,U;
P={M,Z,U}, Q={V,C,D}. Every original tetrahedron has a fixed
vertex-induced paired frame (R,A,B,O,A,B), edge order
(12,13,14,34,24,23), with four distinct actual labels. There are finitely
many original owners. Original faces are paired by a fixed-point-free
involution on face occurrences, with actual-edge-label-preserving face
maps. This allows pairing two distinct faces of the same owner. The
normal quotient is formed from all original edge intervals, pairing
their endpoints through these actual face maps. Original degree means
the number of those intervals, not the valence of the quotient graph.
Sigma=(M,C,D,V,C,D) is the unique flat owner,
with angle pi at M,V and zero at C,D. All other owners are genuine,
with strict paired tests L,J>0 and the paired angle responses used
throughout this continuation.
Tau=(Z,M,C,D,M,C) is a named genuine owner. Every actual edge has
original degree at least six, a connected original normal-circle
quotient, and total angle 2*pi. No simple-link or distinct-role premise
is added; loops, self-gluings, repeated roles and numerical cosh ties
at distinct labels remain permitted.

The source scalar conditions are

    c,d,v>1, m>1+c+d, v<=m-2,
    z>1+m+c, u>m,
    (m-1)*(v-1)>=(c+d)^2,
    u<z+m+1, z<u+m+1.

The two maximum gaps are separate premises here unless supplied by
the complete-star theorem of Sections 318-321 under all its own
hypotheses: a finite actual paired quotient, four distinct labels in
each fixed frame, complete original angle sums, connected normal
circles of original degree at least six, and a wholly genuine star
at a largest actual cosh. Here the larger of Z,U has a wholly genuine
star and every cosh outside {Z,U} is at most m, so that theorem
supplies |z-u|<m+1 when applied in its stated scope. The existing
role-charge results retain their exact scope: in particular the
M/U V/C two-high-axis proof requires original D degree at least six;
the double-P five-slot case with high axis Z uses z<u+m+1, with high
axis U uses u<z+m+1, and with high axis M uses no upper gap. The mixed
four-slot branch and the compensation inequalities use no upper gap.

The exhaustive 360-word table of Sections 402-403 supplies these
necessary role bounds. A transverse C,D pair is genuine nowhere.
The remaining possibilities, using original P-slot count j, are:

| Class | j | P expense |
|---|---:|---|
| A(P0) or B(P0), called cheap axial-P | 1 | theta_P0>0 |
| Sole P transverse label paired with V | 2 | >2*atan(2)>2*pi/3 |
| Sole P transverse label paired with C or D | 2 | >pi |
| Two P labels, both axial | 2 | >pi |
| Two P labels, one axial and one transverse | 3 | >pi |
| Two P transverse labels, both axes low | 4 | >4*pi/3 |
| Three P labels, low label transverse | 4 | >4*pi/3 |
| Three P labels, low label axial | 5 | >4*pi/3 |

The complete table and its scalar and topological dependencies are
given in Sections 402-403. All those hypotheses remain in force here.
In particular, the M/U V/C implication in Section 356 requires
original D degree at least six; the V/D implication in Section 365
does not add an independent degree bound beyond its gap source.

Let a count cheap axial-P owners; n count all other genuine owners;
g=a+n; k count all genuine owners with at least four P slots; and f
count those with five P slots. Every count is an original-owner
multiplicity. Thus 0<=f<=k, and tau is counted in n but not k.
For each P0, keep A(P0) and B(P0) separately even when two numerical
coshes agree. The six counts sum to a.

For each actual label, all original slots continue to count. The
componentwise genuine P degree requirement, in order (M,Z,U), is
(5,6,6), because sigma contributes (1,0,0). Tau contributes (2,1,0),
so the post-tau requirement is (3,5,6). In particular the total genuine
P degree D is at least 17. The total genuine P angle capacity is
5*pi; the individual genuine V,C,D capacities are pi,2*pi,2*pi.

Sections 400 and 404-405 give the owner bounds

    a>=2, f+a>=3, k<=2, g>=6.

We will also derive the discounted degree inequality explicitly below.

## 414. Separate cheap P and low-transverse charges

Define

    X=sum over cheap T of theta_P0(T),
    Y=sum over cheap T of [2*beta_V(T)+2*beta_companion(T)].

X is their exact total P expense. In Y, the companion is C for A(P0)
and D for B(P0). In particular Y uses only genuine V,C,D slots, with
all multiplicities, so

    Y<=pi+2*pi+2*pi=5*pi.                         (414.1)

This is a necessary aggregate bound, not a replacement for the three
individual budgets. The omitted noncheap V,C,D expenses are positive
where present; no such strengthening is needed.

The noncheap owners have D-a original P slots. Every noncheap role
costs strictly more than its P-slot count times pi/3, except that each
five-slot role is charged only four slots. The role table gives

    5*pi-X > (pi/3)*(D-a-f)
             >=(pi/3)*(17-a-f).

Consequently

    X < (pi/3)*(a+f-2).                            (414.2)

Because X>0, this also reproduces a+f>=3. Summing the unconditional
four-theta inequality (407.2) over all cheap owners gives

    2*pi*a < 4*X+Y
             < (4*pi/3)*(a+f-2)+5*pi.

Thus 2*a<4*f+7. Integrality yields

    a<=2*f+3.                                     (414.3)

No low-angle cost was assigned to the wrong actual companion, and no
normal interval or repeated owner was removed in this sum.

## 415. A five-P-slot owner must exist

Suppose f=0. The bound a+f>=3 and (414.3) force a=3. By (414.2),

    X<pi/3.

Each cheap axial angle is positive and bounded by their sum X.
Therefore every one of these three owners satisfies theta_P0<pi/3,
and the conditional three-theta inequality (407.1) applies to all three.
Summing it, using (414.1), gives

    6*pi=2*pi*a < 3*X+Y < pi+5*pi=6*pi,

a contradiction. Hence f>=1. Since f<=k<=2,

    f in {1,2}, and k in {1,2}.                    (415.1)

The proof does not apply the three-theta charge to any owner whose
axial angle has not been proved small.

## 416. Upper bounds on the genuine-owner count

Tau spends more than pi on P and is outside k. Each of the k heavy
owners spends more than 4*pi/3. Each of the other n-k-1 noncheap
owners spends more than 2*pi/3. Therefore n>=k+1 and

    5*pi-X > pi+k*(4*pi/3)+(n-k-1)*(2*pi/3)
            = (pi/3)*(2*n+2*k+1).                 (416.1)

In particular n+k<7, or

    n+k<=6.                                       (416.2)

Combining (416.1) with the unconditional compensation and (414.1),

    2*pi*a < 4*X+Y
      < (pi/3)*(71-8*n-8*k).

The even integer 6*a+8*n+8*k is strictly below 71. Thus

    3*a+4*n+4*k<=35.                              (416.3)

If f=1, (414.3) gives a<=5. If f=2, then k=2 and n>=3, so (416.3)
also gives a<=5. Together with the earlier lower bound,

    2<=a<=5.                                      (416.4)

Since g=a+n, (416.3) reads 3*g+n+4*k<=35. If k=1, n>=2 gives
3*g<=29 and hence g<=9. If k=2, n>=3 gives 3*g<=24 and hence g<=8.
Thus

    6<=g<=9; when k=2, g<=8.                      (416.5)

Including the unique flat sigma, the total original-owner count is
between seven and ten. These are necessary counts under the full
source hypotheses, not realized triangulations.

## 417. Twelve necessary aggregate profiles

The maximum genuine P-slot total for these counts is

    D<=a+5*f+4*(k-f)+3*(n-k)=a+3*n+k+f.

Indeed noncheap owners outside k have at most three P slots. Since
D>=17, one more necessary integer condition is

    a+3*n+k+f>=17.                                (417.1)

Enumerating only the small integer ranges already proved gives exactly
the following twelve tuples (f,k,a,n,g):

    (1,1,2,5,7), (1,1,3,4,7), (1,1,3,5,8),
    (1,1,4,4,8), (1,1,5,4,9),
    (1,2,2,4,6), (1,2,3,4,7), (1,2,5,3,8),
    (2,2,2,4,6), (2,2,3,4,7), (2,2,4,3,7),
    (2,2,5,3,8).

This finite list is exactly the set satisfying

    f in {1,2}, f<=k<=2, 2<=a<=5,
    k+1<=n, n+k<=6, a+n>=6,
    3*a+4*n+4*k<=35, a+3*n+k+f>=17.

For example, the only g=9 profile is f=k=1,a=5,n=4. The list is
merely an aggregate restriction: it does not merge individual labels,
solve the six per-label degree inequalities, assert feasibility of
any role inventory, or produce face pairings. Repeated roles and
self-gluings remain unrestricted by this list.

## 418. High-V weighted original-slot budgets

**Theorem 418.1.** Under all hypotheses of Section 413, the order
v>=max(c,d) is impossible. We use only the unconditional compensation
(407.2) in this high-V proof.

Let a be the number of cheap axial-P owners, meaning the residual
families A(P0)=(P0,V,C,D,V,C) and B(P0)=(P0,V,D,C,V,D), P0 in P.
Let f count genuine owners with five original P slots, k count those
with four or five P slots, and g count all genuine original owners.
The existing role and owner bounds give

    a>=2, 0<=f<=k<=2, g>=6.                     (418.1)

All of these are owner multiplicities, not counts of role vectors.
The total genuine P degree D is at least 17, componentwise at least
(5,6,6) in the order M,Z,U. Tau contributes (2,1,0), leaving the
componentwise post-tau requirement (3,5,6). These three degree
requirements remain distinct even though the proof uses their sum.

Write P_T and V_T for an owner's actual P and V expenses. The full
genuine angle capacities are

    sum P_T=5*pi, sum V_T=pi.

Consequently the weighted charge W_T=2*P_T+V_T has total capacity

    sum W_T=11*pi.                               (418.2)

Each original axial slot is counted once; a transverse label has two
original slots. Self-gluings do not change these angle sums.

## 419. Every high-V cheap owner costs more than pi

For a cheap owner, let r>=m be its high axis, let a0 be its C or D
transverse companion, and let b be its opposite low axis. The source
bounds give r>=max(v,a0)+2. Under v>=max(c,d), v>=a0.

The paired-angle formula directly gives beta_V>=beta_companion.
Indeed, with x=sqrt(L/J)>0 and

    Kminus=(sqrt(v^2-1)-sqrt(a0^2-1))/(v+a0)>=0,

their difference is 2*atan(Kminus*x)>=0. This includes the equality
v=a0; it is a numerical angle comparison, not an identification of
actual labels.

Applying (407.2),

    4*theta_P0+4*beta_V
      >=4*theta_P0+2*beta_V+2*beta_companion>2*pi.

For this owner P_T=theta_P0 and V_T=2*beta_V. Therefore

    W_T=2*theta_P0+2*beta_V>pi.                   (419.1)

## 420. The weighted degree discount forces a=f=2

The noncheap owners have D-a original P slots. The role table of Section 402
charges each such slot strictly above pi/3, except that each five-slot
owner is discounted by one slot. Thus their total P expense satisfies

    P_noncheap>(pi/3)*(D-a-f)
                >=(pi/3)*(17-a-f).

Every noncheap V expense is nonnegative. Summing (419.1) and using (418.2),

    11*pi >= 2*P_noncheap+sum_cheap W_T
           >(2*pi/3)*(17-a-f)+pi*a
           =(pi/3)*(34+a-2*f).

Hence a<2*f-1. Since a,f are integers,

    a<=2*f-2.

Together with a>=2 and f<=2, this forces

    a=f=k=2.                                    (420.1)

No upper bound on repeated role multiplicities was assumed in making
this deduction.

## 421. The strict high-V six-owner contradiction

Each of the k=2 heavy owners has P expense greater than 4*pi/3,
and hence W expense greater than 8*pi/3.

Every genuine owner that is neither cheap nor heavy spends more than
2*pi on W. For all such roles except the transverse P/V class, its
P expense is already greater than pi. For the transverse P/V class,
the exact estimates of Section 380 are

    P_T>2*atan(2), P_T+V_T>4*atan(2).

Thus W_T=P_T+(P_T+V_T)>6*atan(2)>2*pi, because
atan(2)>atan(sqrt(3))=pi/3.

Since g>=6 and the two cheap owners and two heavy owners are disjoint,
there are at least two further genuine owners of this latter class.
Counting only those six original owners gives

    sum W_T>2*pi+2*(8*pi/3)+2*(2*pi)
            =34*pi/3>11*pi,

contradicting (418.2). This proves the high-V exclusion.

## 422. The remaining strict middle-V order

Sections 382-385 exclude v<=min(c,d) under the full source hypotheses
of Section 413. Theorem 418.1 excludes v>=max(c,d). Therefore the only
remaining numerical orders are

    d<v<c or c<v<d.

All equality cases are already excluded, including c=d and v equal
to either low companion. This is a comparison of numerical coshes;
the actual labels remain distinct even when their values coincide.
The source tau distinguishes C and D and is never symmetrized here.

**Theorem 422.1.** Under all hypotheses of Section 413, neither strict
middle order is possible. The proof uses both compensation bounds:
the unconditional four-theta estimate (407.2), and the conditional
three-theta estimate (407.1) only after proving the relevant axial
angles are at most pi/3.

## 423. Every middle-V cheap owner has the same actual companion

A cheap axial-P owner means A(P0)=(P0,V,C,D,V,C) or
B(P0)=(P0,V,D,C,V,D), where P0 is M,Z or U. The strict opposite-axis
ordering lemma in Section 383 says every genuine owner of either form
has v greater than its opposite low axis. This lemma is a scalar
consequence of the source product and strict genuineness; it does not
assume that the owner receives a source face.

Consequently:

- if d<v<c, all cheap owners are A(P0), with transverse companion C;
- if c<v<d, all cheap owners are B(P0), with transverse companion D.

Let A0 denote this larger actual low companion and B0 the smaller
opposite low axis. These names do not interchange C,D in tau. There
is only one cheap family in either order, but its M,Z,U owner counts
remain separate.

Let a count cheap owners, f count five-P-slot owners, k count owners
with at least four P slots, n count noncheap genuine owners and g=a+n.
The bounds from Sections 400 and 405 are a>=2, f<=k<=2 and g>=6. Define

    X=sum_cheap theta_P0,
    Y=sum_cheap (2*beta_V+2*beta_A0).

The common-companion capacities now give the sharper bound

    Y<=pi+2*pi=3*pi.                              (423.1)

This uses exactly the V and A0 budgets, not a combined C,D allowance.
Let D_P be the total genuine original P degree. Its componentwise
lower bound is (5,6,6), in order M,Z,U, and D_P>=17. Tau contributes
(2,1,0), so the post-tau deficits remain (3,5,6).

The noncheap role charges give

    5*pi-X>(pi/3)*(D_P-a-f)
              >=(pi/3)*(17-a-f),
    X<(pi/3)*(a+f-2).                             (423.2)

## 424. Exactly two five-slot owners and two aggregate alternatives

Summing the unconditional four-theta bound (407.2) and using (423.1)-(423.2),

    2*pi*a<4*X+Y<(4*pi/3)*(a+f-2)+3*pi.

Thus 2*a<4*f+1, and integer counts give a<=2*f. Since a>=2 and
f<=2, either f=1,a=2 or f=2,2<=a<=4.

If f=1,a=2, (423.2) gives X<pi/3. Every cheap axial angle is then
less than pi/3. The conditional three-theta bound (407.1) yields

    4*pi=2*pi*a<3*X+Y<pi+3*pi=4*pi,

a contradiction. Hence

    f=k=2, 2<=a<=4.                              (424.1)

There are at least three noncheap owners: the two five-slot owners
and tau. If n>=5, these three plus two other noncheap owners spend
more than

    2*(4*pi/3)+pi+2*(2*pi/3)=5*pi

on P, which is impossible. Thus n is three or four.

If n=4, the noncheap expense exceeds
2*(4*pi/3)+pi+2*pi/3=13*pi/3, so X<2*pi/3. The unconditional compensation (407.2) gives
2*pi*a<4*X+Y<17*pi/3, hence a<=2. Thus

    (a,n,g)=(2,4,6).                             (424.2)

If n=3, the only noncheap owners are tau and the two five-slot
owners. They contribute exactly 3+5+5=13 original P slots. Since
D_P>=17 and each cheap owner contributes one, a>=4. Together with
(424.1), this gives

    (a,n,g)=(4,3,7).                             (424.3)

## 425. The extra six-owner role must be transverse P/V

In (424.2), let T be the noncheap owner other than tau and the two
five-slot owners. It is not heavy, since k=2. If its P expense were
greater than pi, those four noncheap owners would spend more than
2*(4*pi/3)+2*pi=14*pi/3, leaving X<pi/3. Both cheap axial angles
would be less than pi/3, and their conditional compensation (407.1) would
again give 4*pi<3*X+Y<4*pi.

By the exhaustive role table, the only noncheap, nonheavy class not
already proved to spend more than pi on P is

    C(P0)=(C,P0,V,D,P0,V), P0 in {M,Z,U}.

Therefore T must have this transverse P/V form. It has exactly two
original P slots. In (424.2) we consequently have D_P=13+2+2=17;
in (424.3) we already have D_P=13+4=17. Since the componentwise lower
bounds sum to 17, both alternatives have exact genuine P degrees

    (degree_M,degree_Z,degree_U)=(5,6,6).          (425.1)

No assumption that all C(P0) owners cost at most pi is used: if the
specific owner costs more than pi, that instance is excluded too.

## 426. The seven complete per-high-label profiles

For the two five-slot owners, let e=(e_M,e_Z,e_U) count their high
axial labels; e_M+e_Z+e_U=2. Each such owner contains all three
P labels, with one at its high axis and the other two transverse.
Thus their combined P degree is (4,4,4)-e. Adding tau gives

    (6-e_M,5-e_Z,4-e_U).                         (426.1)

Let x=(x_M,x_Z,x_U) count the cheap owners' high axes. In the
seven-genuine-owner alternative, equations (425.1)-(426.1) imply

    x=(e_M-1,1+e_Z,2+e_U).

Nonnegativity and e_M+e_Z+e_U=2 give exactly three profiles:

| e | x |
|---|---|
| (2,0,0) | (1,1,2) |
| (1,1,0) | (0,2,2) |
| (1,0,1) | (0,1,3) |

In the six-genuine-owner alternative, if the extra C(P0) label is
q in {M,Z,U}, it contributes twice the corresponding unit vector u_q.
The exact equation is

    x=(e_M-1,1+e_Z,2+e_U)-2*u_q.

There are exactly four nonnegative profiles:

| e | q | x |
|---|---|---|
| (2,0,0) | U | (1,1,0) |
| (1,1,0) | Z | (0,0,2) |
| (1,1,0) | U | (0,2,0) |
| (1,0,1) | U | (0,1,1) |

These lists can also be checked without enumeration: the M component
of either equation forces e_M>=1, and only the three listed e vectors
then remain. Subtracting two units in each possible q component gives
exactly the four six-owner rows. In particular, every surviving
profile has at least one five-slot owner with high axis M.

## 427. All remaining original face types

A fixed paired frame (R,A,B,O,A,B) has exactly two original faces
with edge-label triple {R,A,B} and two with triple {O,A,B}.
All three labels on each face are distinct. In the remaining inventory
the possibilities are therefore precisely:

| Owner | Its two face triples, each occurring twice |
|---|---|
| sigma | MCD, VCD |
| tau | ZMC, DMC |
| cheap A(P0) | P0VC, VCD |
| cheap B(P0) | P0VD, VCD |
| extra C(P0), if present | CP0V, DP0V |
| five-slot owner, high axis H, low axis L | MZU, L(P minus H) |

There are no other owners in either inventory. Here L is one of the
three actual low labels V,C,D. The table describes actual labels,
not merely cosh values, so numerical ties cannot create another face
match. Repeated rows and self-gluings have not been removed.

## 428. An M-axial five-slot owner forces the other one to match

Choose the five-slot owner rho whose high axis is M, whose existence
was just proved. Write its low axis as L. Its frame is

    (M,Z,U,L,Z,U)

up to interchanging its axes and its two transverse labels. Its two
L-end original faces have label triple LZU. The face table shows that
no owner outside the two five-slot owners can have an LZU face:
sigma, cheap owners and C(P0) have at most one P label on each face;
tau's only two-P face has M,Z, not Z,U.

The two LZU faces of rho cannot be paired to each other. If they were,
the unique original L-edge normal interval in rho would have both
endpoints glued to each other. It would be a closed one-interval
component of the actual L normal quotient. No further normal interval
could attach, since both original face endpoints have already been
paired. Connectedness would make this the whole L circle, of original
degree one, contradicting original degree at least six.

In the canonical frame, the two L faces are 134 and 234. Their
unique label-preserving internal map is 1->2, 3->4, 4->3, which
reverses the parametrization of the L edge 34. This does not change
the fact that the two face-incidence endpoints belong to its one
original normal interval.

This argument uses endpoints corresponding to face incidences, not
the endpoints of the actual edge in the vertex quotient. A face map
may reverse the parametrization of L or exchange its two vertices;
it still pairs the two ends of the same normal interval. Loops and
orientation-reversing self-gluings therefore do not evade the closed-
component conclusion. Distinct-face self-gluings were allowed and have
been analyzed, rather than excluded by an extra simplicity premise.

At least one LZU face of rho must consequently be paired to a face
of the other five-slot owner rho'. For rho' to have such a face, its
two transverse high labels must be Z,U, so its high axis is also M;
its low axis must be the same actual L. Thus rho' has the same paired
role (M,Z,U,L,Z,U). Repeated roles are allowed; the contradiction
below is topological, not a prohibition on duplicating this role.

## 429. Two original M intervals form a closed subcollection

The face table shows that MZU faces occur only in rho and rho'.
In both owners the unique original M occurrence is axial. Every
endpoint of each of their two original M normal intervals belongs to
an MZU face. Its paired face is again an MZU face in rho or rho', and
the unique M edge in that face is the selected axial M edge.

Hence these two original intervals are closed under every endpoint
pairing. Their endpoint quotient is a nonempty union of closed
components of the actual M normal circle. This statement allows any
pairing of the four endpoints, including self-gluings, and any
orientation of the face maps. No transition can leave the selected
two-interval set.

For completeness, write the two intervals' endpoint sets as
{i0,i1} and {j0,j1}. The three possible pairings are

    {i0-i1, j0-j1}, {i0-j0, i1-j1}, {i0-j1, i1-j0}.

The first gives two separate one-interval circles; either cross-pairing
gives a two-interval circle. Reversing an edge orientation changes no
endpoint incidence in this list. Thus internal self-gluings and both
cross-gluing alternatives are included explicitly.

Since the actual M normal quotient is a connected circle, a nonempty
closed collection of its original intervals must be the whole circle:
all endpoint pairings stay inside it and every normal-link vertex has
the two incidences prescribed by the interval pairing. Its original
degree would therefore be at most two; the internal-pairing case
already contradicts connectedness. This contradicts degree at least six;
also sigma and tau already supply original M intervals outside this
set. The selected subcollection cannot be joined to those intervals
without an endpoint pairing absent from the exhaustive face table.

This completes the middle-V contradiction. The last two topological
steps only need original degree(L)>=2 and degree(M)>=3 once the
inventory is known; the full source hypotheses supply much more and
are retained because the preceding expense results need them.

## 430. Exclusion of the stated six-edge source normal form

**Theorem 430.1 (source-normal-form exclusion).** No finite actual
paired quotient satisfies all the hypotheses of Section 413.

Indeed the numerical orders v<=min(c,d), v>=max(c,d), and
min(c,d)<v<max(c,d) cover every case, including ties. The first is
excluded by Sections 382-385, the second by Theorem 418.1, and the
third by Theorem 422.1. The last contradiction uses the actual
face-pairing transitions of original normal intervals, after the
exact owner and per-label inventories have been proved.

The complete dependency chain is explicit: the paired scalar
compensation in Sections 407-412 combines with the original-slot role
charges of Sections 402-403, the degree and owner bounds of Sections
404-405, and the source hypotheses of Section 413. These give the
weighted high-V contradiction and the two middle-V inventories.
The seven per-label profiles force an M-axis five-slot owner; its
low-axis face pair forces the other five-slot owner to have the same
role; their M-face pairs close a proper collection of actual normal
intervals, contradicting the connected-circle hypothesis.

This resolves the source-normal-form boundary recorded in Sections
401-406. It retains six distinct actual labels, one four-distinct
fixed frame per owner, the unique flat sigma and named genuine tau,
both explicitly scoped maximum gaps, all original degree and angle
conditions, and the face-occurrence and connected-circle hypotheses.
Loops, distinct-face self-gluings, repeated role vectors, and numerical
ties at distinct labels were included throughout.

Any broader intrinsic six-edge flat-exclusion or general CFMP
geometric-realization theorem additionally requires a valid reduction
to this exact normal form under that theorem's own hypotheses. No
omitted reduction, source-face existence assertion, complete-star
premise, or lower-reservoir theorem is silently promoted here. The
arguments are pure mathematical derivations and do not constitute
Lean or kernel verification.

## 431. A reusable transverse-dominance expense

**Theorem 431.1.** Let r,p,a,b>1 and consider the paired frame
(r,p,a,b,p,a), with strict genuine factors

    L=(p+a)^2-(r-1)*(b-1)>0,
    J=(r+1)*(b+1)-(p-a)^2>0.

Let theta_r be its axial angle at r and beta_p its transverse angle
at p, with the usual paired hyperideal response formulas. Assume

    p>=a+b.                                           (431.1)

Then

    theta_r+2*beta_p>pi.                               (431.2)

No lower bound on r besides r>1 and strict genuineness is needed.
No source, maximum gap, degree, normal circle or face receiver is
assumed. The two transverse p occurrences are counted separately.
The argument is a scalar consequence of the paired response formulas.

## 432. The exact angle-sign criterion

Put

    D_r=r^2+p^2+a^2+2*r*p*a-1,
    D_b=b^2+p^2+a^2+2*b*p*a-1,
    N=a*(r+b)+p*(r*b+a^2-p^2+1).

For the genuine angles,

    cos(beta_p)=N/sqrt(D_r*D_b),
    sin(beta_p)=sqrt((p^2-1)*L*J)/sqrt(D_r*D_b),
    cot(theta_r/2)=sqrt((r+1)*L/((r-1)*J)).

The sine identity follows from the exact polynomial identity

    D_r*D_b-N^2=(p^2-1)*L*J.                         (432.1)

If N<=0, then beta_p>=pi/2, and theta_r>0 proves (431.2).
Suppose N>0. Then beta_p is in (0,pi/2), while theta_r/2 is in
(0,pi/2). The target (431.2) is equivalent to

    beta_p>pi/2-theta_r/2,
    tan(beta_p)>cot(theta_r/2).

All factors used in this comparison are positive. Squaring and
cancelling L>0 shows that it suffices, and is equivalent, to

    Delta=(p^2-1)*(r-1)*J^2-(r+1)*N^2>0.           (432.2)

## 433. An affine factorization in the high axis

Direct expansion gives

    Delta=D_r*F(r), F(r)=A*r+B,                    (433.1)

where

    A=(2*b+1)*p^2-2*a*b*p-a^2-b^2-2*b-1,
    B=-2*a^2*p^2+a^2-2*a*b*p+4*a*p^3-4*a*p
      -b^2+2*b*p^2-2*b-2*p^4+3*p^2-1.

Under p>=a+b, the coefficient A is strictly positive. Indeed

    dA/dp=2*((2*b+1)*p-a*b)>0,
    A at p=a+b
      =2*a*b*(b+1)+2*b*(b^2-1)-1>3>0.             (433.2)

The last strict comparison uses a,b>1. Thus F is strictly increasing
as a function of r on the whole real line. This is an algebraic
monotonicity, not an unproved monotonicity of the angle expense.

## 434. Comparison at the zero of the cosine numerator

The numerator N is affine in r with positive slope a+p*b. At r=1,

    N(1)=a*(1+b)+p*(b+a^2-p^2+1).

For p>=a+b, this is strictly negative. To verify it, its derivative
with respect to p is b+a^2+1-3*p^2, which is at most

    1+b-2*a^2-6*a*b-3*b^2<0.

At the boundary p=a+b, exact factorization gives

    N(1)=-(2*a+b)*(a*b+b^2-b-1)<0,                 (434.1)

because a*b>b and b^2>1. Therefore the unique zero of N as a
function of r is

    r0=[p*(p^2-a^2-1)-a*b]/(a+p*b)>1.             (434.2)

Our current branch N>0 implies r>r0. The following comparison does not
require the genuine tests at r0; it is a polynomial identity evaluated
at that rational point. Since D_r0>0 and r0>1, (433.1) gives

    D_r0*F(r0)=(p^2-1)*(r0-1)*J(r0)^2>=0.

Thus F(r0)>=0. By the strict positive slope A and r>r0,

    F(r)>F(r0)>=0.

Equation (433.1) yields Delta>0, proving the angle comparison (432.2)
and hence (431.2). Both signs of N have been handled, including N=0.

## 435. Exact high/low separation in the near-maximal range

Let the six distinct actual labels be M,V,Z,U,C,D, with corresponding
coshes m,v,z,u,c,d. Suppose

    c,d>1, m>=v>1, z,u>=m,
    v>m-2, (m-1)*(v-1)>=(c+d)^2.                  (435.1)

Set H={M,V,Z,U}. Since m<v+2, the product gives

    (c+d)^2< (v+1)*(v-1)=v^2-1.

Consequently

    v>sqrt(5)>2, c+d<v, c,d<v-1,                 (435.2)

and every H value is at least v. Every pair of distinct H labels,
with values r,p, also satisfies

    (r-1)*(p-1)>=(m-1)*(v-1)>=(c+d)^2.            (435.3)

Indeed V is a least H value and all other H values are at least m.
This retains the actual distinct-label product constraint. It does
not replace both factors in (435.3) by v-1.

The later role argument uses only the following reusable conditions,
which (435.1)-(435.3) supply with s=v:

    c,d>1; every H value is at least s>c+d;
    (r-1)*(p-1)>=(c+d)^2 for every distinct H pair. (435.4)

Conditions (435.4) imply s>2 and c,d<s-1. The pairwise product is a
separate hypothesis, not inferred merely by lowering both high values
to s. It can equivalently be checked on the two least H values at
distinct labels. This separates the direct four-high theorem from
the specific near-maximal sufficient conditions.

## 436. Two high transverse labels and two low axes

Consider a genuine frame (r,p,q,o,p,q) with

    p,q>=s>2, 1<r,o<=s-1.

Let S=beta_p+beta_q and K=(sqrt(p^2-1)+sqrt(q^2-1))/(p+q).
The exact paired response is S=2*atan(K*sqrt(L/J)), where

    L=(p+q)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(p-q)^2>0.

The scalar bounds imply

    L>=4*s^2-(s-2)^2=3*s^2+4*s-4>3*s^2,
    J<=s^2,
    K^2>=1-1/s^2>3/4.

For K, apply sqrt(x^2-1)>=x*sqrt(1-1/s^2) separately at x=p,q.
Thus K^2*L/J>9/4>1. Since atan is increasing on positive reals,
S>pi/2. The four original high transverse slots therefore obey

    2*beta_p+2*beta_q>pi.                          (436.1)

No condition on the ordering of p and q is needed, including p=q.

## 437. Three high labels with the low label transverse

Let

    r,p,o>=s>2, 1<q<=s-1,
    L=(p+q)^2-(r-1)*(o-1)>0,
    J=(r+1)*(o+1)-(p-q)^2>0.

In the genuine paired frame (r,p,q,o,p,q), define its four-high-slot
expense E=theta_r+theta_o+2*beta_p. Then

    E>4*pi/3-4/s^2>pi.                            (437.1)

Compared with Sections 395-399, the low-label gap is now one rather
than two, with a weaker
expense conclusion. It does not assume monotonicity of E.

## 438. Distortion of an angle for every u>2

For u>2 put a0=sqrt(1-u^(-2))>1/2. If phi,psi in (0,pi) have
positively oriented vectors proportional to (cos(phi),sin(phi))
and (cos(phi),a0*sin(phi)), respectively, then

    |psi-phi|<1/u^2.                              (438.1)

Their difference delta has absolute value less than pi/2. The exact
angle-between-vectors formula gives

    tan(|delta|)=(1-a0)*|sin(phi)*cos(phi)|
                  /(cos(phi)^2+a0*sin(phi)^2)
                <=(1-a0)/(2*sqrt(a0)).

The inequality follows from (|cos(phi)|-sqrt(a0)*sin(phi))^2>=0.
Since |delta|<=tan(|delta|) and 1-a0=1/[u^2*(1+a0)],

    |delta|<=1/[2*u^2*sqrt(a0)*(1+a0)]<1/u^2.

This covers phi=pi/2 and the zero-distortion case too. The proof
requires only u>2, rather than importing the earlier u>3 domain.

## 439. Exact axial-pair reduction and comparison branch

Define local auxiliary scalars

    z0=sqrt((r+1)*(o+1)), y0=sqrt((r-1)*(o-1)),
    h=(z0+y0)/2, k=(z0-y0)/2.

Then

    h>=s, 1<=k<=h/s.                              (439.1)

The first bound follows from z0>=s+1 and y0>=s-1. The identity
z0^2-(y0+2)^2=2*(sqrt(r-1)-sqrt(o-1))^2>=0 proves k>=1.
Finally y0/z0>= (s-1)/(s+1) gives k/h<=1/s.

Put alpha=(theta_r+theta_o)/2, X=sqrt(L*J)>0, and

    Np=p*(h^2+k^2+q^2-p^2)+2*q*h*k,
    Nh=h*(p^2+q^2+k^2-h^2)+2*k*p*q.

The original genuine factors are

    L=(p+q)^2-(h-k)^2,
    J=(h+k)^2-(p-q)^2.

The exact half-angle identities, obtained by tangent addition, are

    cot(alpha)=Nh/(sqrt(h^2-1)*X),
    cot(beta_p)=Np/(sqrt(p^2-1)*X).               (439.2)

For example, with a_r=sqrt((r-1)/(r+1)), a_o similarly, one has
a_r*a_o=(h-k)/(h+k) and a_r+a_o=2*sqrt(h^2-1)/(h+k).
These give the first formula. The second uses the sum and product
of the two transverse arctangent coefficients. Both sines are
positive, so the cotangent formulas retain right-angle cases.

Define alpha0,beta0 in (0,pi) by cot(alpha0)=Nh/(h*X) and
cot(beta0)=Np/(p*X). Applying (438.1) at u=h,p gives

    E/2=alpha+beta_p>alpha0+beta0-2/s^2.           (439.3)

Let T0=alpha0+beta0. Initially T0 is in (0,2*pi), and

    cot(alpha0)+cot(beta0)
      =[2*(q^2+k^2)+2*q*k*(p/h+h/p)]/X>0.

As both individual sines are positive, this implies sin(T0)>0,
hence T0 is in (0,pi). Exact polynomial identities are

    Np^2+p^2*L*J
      =4*(h*k+p*q)*(h*p+k*q)*(h*q+k*p),
    Nh^2+h^2*L*J
      =4*(h*k+p*q)*(h*p+k*q)*(h*q+k*p),
    Np*Nh-p*h*L*J
      =-2*(h*k+p*q)*(h*q+k*p)*(h^2+p^2-q^2-k^2).

Their positive normalization gives

    cos(T0)=-(h^2+p^2-q^2-k^2)/(2*(h*p+k*q)).     (439.4)

## 440. A positive quadratic for the one-unit gap

The expression q^2+k^2+k*q increases in both positive variables.
Using q<=s-1 and k<=h/s, we obtain

    h^2+p^2-q^2-k^2-h*p-k*q
      >=(1-1/s^2)*h^2+p^2-h*p
         -(s-1)^2-h*(s-1)/s.

Write A0=h-s>=0 and B0=p-s>=0. The last expression equals

    s-1+(s-1-1/s)*A0+s*B0
      +(1-1/s^2)*A0^2+B0^2-A0*B0.                (440.1)

Here s-1>0, s-1-1/s>0, and s>0. Since s>2, the quadratic
part is at least

    (3/4)*A0^2+B0^2-A0*B0
      =(1/4)*A0^2+(1/2)*B0^2+(1/2)*(A0-B0)^2>=0.

Thus h^2+p^2-q^2-k^2>h*p+k*q. By (439.4), cos(T0)<-1/2.
The established T0 in (0,pi) gives T0>2*pi/3. Equation (439.3)
therefore proves E>4*pi/3-4/s^2. Since s>2 and pi>3,

    4*pi/3-4/s^2>4*pi/3-1>pi.

This completes (437.1), including all sign branches of Nh and Np and
all ties among the three high values.

## 441. A high axis and two high transverse labels

Suppose a genuine frame (r,p,q,o,p,q) has r,p,q>=s>2. The other
axis o is arbitrary above one. Let theta=theta_r and S=beta_p+beta_q.
Put

    K=(sqrt(p^2-1)+sqrt(q^2-1))/(p+q),
    lambda=K*sqrt((r-1)/(r+1)), t=cot(theta/2)>0.

The exact response is S=2*atan(lambda*t). Moreover

    K>=sqrt(1-1/s^2),
    lambda>=(s-1)/s>1/2.                         (441.1)

We claim S>atan(t). If S>=pi/2 this is immediate. Otherwise S is
in (0,pi/2), its tangent denominator is positive, and

    tan(S)=2*lambda*t/(1-lambda^2*t^2)>t.

Indeed 2*lambda>1 and the denominator is positive and at most one.
Strict monotonicity of tangent on (0,pi/2) proves the claim. Since
theta+2*atan(t)=pi, it follows that

    theta_r+2*beta_p+2*beta_q>pi.                  (441.2)

These are five original high slots. The sixth slot is nonnegative
and may itself be high. This lemma therefore covers both a three-high
frame with its low label axial and a frame with all four labels high.

## 442. The complete four-high role partition

Under (435.4), a frame with four distinct actual labels contains at
least two H labels, because the complement has only C,D. The complete
fixed-word partition is:

| High-label placement | Fixed words | High slots | Conclusion |
|---|---:|---:|---|
| Two high labels, both axial; C,D transverse | 24 | 2 | Not genuine |
| Two high labels, one axial and one transverse | 96 | 3 | >pi by Sections 431-434 |
| Two high labels, both transverse; C,D axial | 24 | 4 | >pi by Section 436 |
| Three high labels, low label transverse | 96 | 4 | >pi by Sections 437-440 |
| Three high labels, low label axial | 96 | 5 | >pi by Section 441 |
| Four high labels | 24 | 6 | >pi by Section 441 and positivity |

The six counts sum to 360. With exactly two high labels there are
six choices of their pair, and their four positions give counts
4,16,4 per choice. With three high labels there are four choices
of high triple and two choices of low label; twelve permutations
place that low label axially and twelve transversely. With four high
labels there are 24 permutations.

For the first row, the distinct actual high axes obey (435.4), so
L=(c+d)^2-(r-1)*(o-1)<=0; strict genuineness fails. In the second
row, the transverse high p is at least s>c+d, so Theorem 431.1 in
Sections 431-434 applies with {a,b}={c,d}. In every later row use the
same s>2, with each low value strictly below s-1. This proves
that every genuine owner spends strictly more than pi on H.

The census is by fixed actual label words, before numerical
coincidences. Original owners with repeated role vectors remain
separate. Every axial occurrence counts once and every transverse
label has its two separate original slots. No receiver, distinct-role
assumption, or prohibition on loops or self-gluings is introduced.

## 443. A reusable direct four-high exclusion theorem

Assume a finite actual face-paired tetrahedral quotient with exactly
six distinct actual labels M,V,Z,U,C,D. Each original owner has a
fixed vertex-induced paired frame with four distinct actual labels.
Assume one common positive length field with coshes satisfying (435.4),
and complete original angle sums 2*pi at every actual edge.

Assume sigma=(M,C,D,V,C,D) is the unique flat owner, with angle pi
at its M,V axes and zero at its four transverse slots. Every other
owner is genuine, with strict L,J>0 and the usual paired response
angles. As for genuine hyperideal paired tetrahedra throughout the
published theory, each genuine owner's six-slot total is less than
2*pi. This follows by adding its two vertex-link inequalities
theta_r+beta_p+beta_q<pi and theta_o+beta_p+beta_q<pi.

**Theorem 443.1.** No such quotient and length field exist.

Proof. Let g be the number of genuine original owners. The six complete
angle sums total 12*pi, and sigma contributes 2*pi. Therefore

    10*pi=sum_genuine total_six_slot_angle<2*pi*g,
    g>=6.                                               (443.1)

The four actual H labels have total angle capacity 8*pi. Sigma
contributes pi at each of M,V and nothing at Z,U. Thus

    sum_genuine expense_H=6*pi.                          (443.2)

The exhaustive role partition proves expense_H>pi for every genuine
owner. Hence (443.1)-(443.2) give

    6*pi=sum_genuine expense_H>g*pi>=6*pi,

a contradiction.

Once this unique-flat normal form is given, the direct contradiction
does not use the near-maximal inequality, a named source tau, either
maximum gap, an original degree lower bound, or connected-circle
topology. Those hypotheses are needed
by the earlier reductions supplying the normal form, not by this last
strict-capacity argument. The scalar hypotheses here permit numerical
ties such as m=v and z=u; actual labels remain distinct.

## 444. The exact intrinsic six-edge ambient class

For the next deduction retain the full ambient class of the earlier
paired-reservoir volume. Let N be a connected orientable compact
3-manifold with nonempty boundary, every component a closed surface
of genus at least two. Fix an actual finite ideal face-pairing
triangulation of N whose ideal vertex links are those boundary
surfaces. Original faces are paired by a fixed-point-free involution
on their occurrences. The actual normal quotient is formed by pairing
the endpoints of the original local edge intervals through those face
maps. Each actual edge has a connected circular normal link and
original degree at least six.

Suppose there are exactly six actual global edge labels. In every
original tetrahedron choose one fixed vertex-induced paired frame,
in edge order (12,13,14,34,24,23), of the form

    (R,A,B,O,A,B), with R,A,B,O four distinct actual labels.

Assume one common positive global generalized length field has every
original edge-angle sum equal to 2*pi. The usual positive-length
classification makes each owner genuine or flat with two opposite
pi angles and four zeros. All original occurrences count, including
repeated visits, loops, parallel face pairings and distinct-face
self-gluings. Numerical ties at distinct labels are permitted.

These are the common ambient hypotheses for the following binding;
no ambient topology assumption from the earlier volume is removed.
The direct scalar/angle theorem of Section 443 needed less topology
once its unique-flat normal form was already supplied.

## 445. Published reductions to the whole source range

Suppose a flat exists in the class of Section 444. In the framework
of Section 130, take the reservoir part to be all of E and the special
part to be empty. This is allowed even if a label
happens to occur only axially; no transverse witness is presumed.
Sections 132-134 choose M maximal among all pi-selected reservoir
labels and provide four distinct actual labels M,Z,C,D and a genuine
source tau with

    tau=(Z,M,C,D,M,C), p_M=1, p_Z=0,
    m>=1+c+d, z>=1+m+c>m.

Here p_e counts original flat pi slots. In particular c,d<m-2.
Section 182 provides an additional upper-threshold reservoir.
Sections 296-298 and 304-307 then prove that every one of the six
reservoirs has a genuine occurrence and every flat is axial-selected.
The degree-eight strengthening mentioned earlier is unnecessary.

Sections 314-316, under the four-distinct-frame hypothesis, provide
a second actual label U with u>m. Section 317 shows that the source
flat's other axis is the sixth label V, and proves globally that
sigma is the unique flat owner and the only owner with fixed pair
C,D. Thus

    sigma=(M,C,D,V,C,D), 1<v<=m,
    (m-1)*(v-1)>=(c+d)^2,
    u>m, z>=1+m+c,

and every other original owner is genuine. In particular Z,U have
wholly genuine stars. This published reduction covers both ranges
v<=m-2 and m-2<v<=m; it does not itself exclude the latter.

Sections 318-321 apply the complete-star maximum-gap theorem to the
larger of Z,U. Every cosh outside those two labels is at most m, and
the two largest other values are min(z,u) and m. With all the actual
degree, circle and complete-angle hypotheses retained, this gives

    |z-u|<m+1,
    u<z+m+1 and z<u+m+1.                          (445.1)

This is the source of both strict one-sided gaps used by the
low-sixth proof. They are not inferred from a local scalar relaxation.

## 446. Binding the two source ranges without a hidden strictness premise

First suppose v<=m-2. If m=1+c+d, then the source-flat product gives

    (c+d)*(v-1)>=(c+d)^2,
    v>=1+c+d=m,

contradicting v<=m-2. Hence m>1+c+d.

The genuine source tau has two original transverse M slots and sigma
already contributes pi at M. Therefore 2*beta_M(tau)<=pi. Its cosine
has positive denominator and numerator

    N(z)=c*(z+d)+m*(z*d+c^2-m^2+1).

This affine function has derivative c+m*d>0. At z0=1+m+c,

    N(z0)=[c+m*(1+m+c)]*(1+c+d-m)<0.

The source angle budget gives N(z)>=0, forcing z>1+m+c. This is the
strict clause of the original escape theorem in Section 134. The
remaining conditions of Section 413 follow from Section 444, the
published reductions, and (445.1). Thus Theorem 430.1 excludes the
entire low-sixth subcase. No receiver inventory is inserted here.

Now suppose m-2<v<=m. Section 435 gives

    c+d<v, v>2,
    all four M,V,Z,U values >=v,
    every distinct high-pair shifted product >=(c+d)^2.

These are exactly the scalar conditions of Theorem 443.1 with s=v.
The unique flat and the complete original angle sums are supplied by
the same reduction. That direct theorem therefore excludes this
remaining near-maximal range, without using the strict-source
upgrades or either maximum gap in this second branch.

The equality m=1+c+d forces v=m by the source product and v<=m;
it is consequently included in this second branch. This necessary
equality implication is not an assertion that the boundary is
realizable. Equal numerical coshes and the endpoint v=m-2 are all
covered by the displayed disjoint split.

## 447. Flat exclusion for exactly six actual edges and four-distinct frames

**Theorem 447.1.** Under all hypotheses of Section 444, every original
tetrahedron of the common positive generalized length field is genuine.

Proof. A nonempty flat set would give the source data of Section 445.
Its entire range 1<v<=m is the union of the two cases excluded in
Section 446. Thus no flat exists, and the positive-length classification
leaves only genuine owners.

The proof includes all actual original slots and face occurrences.
It neither removes repeated visits nor forbids two distinct owners
from having the same role vector. The four-distinct-label condition
is a condition within each fixed frame, not an assumption that the
four numerical coshes differ or that owners have different roles.

This theorem completes flat exclusion for the stated intrinsic
six-actual-edge class. It does not extend the 360-word census to
repeated axial/frame labels, to six reservoir labels with additional
special actual edges, or to more than six actual labels. The original
degree and topology hypotheses remain those of Section 444.

Existence of a common positive critical length field and conversion
to a geometric realization are separate inputs and are not proved by
this flat-exclusion argument alone. No unrestricted CFMP theorem or
Lean/kernel verification is asserted.

## 448. The exact six-edge realization class

Let N be a connected orientable compact 3-manifold with nonempty
boundary, every component a closed surface of genus at least two.
Fix an actual finite ideal face-pairing triangulation whose ideal
vertex links are those boundary surfaces. Original faces are paired
by a fixed-point-free involution on their occurrences, with the
prescribed vertex maps. Every actual edge has a connected circular
normal link formed from its original local edge intervals, and its
original degree, counting every occurrence, is at least six.

Suppose the actual global edge set E has exactly six elements. In
every original tetrahedron fix a vertex-induced frame, in order
(12,13,14,34,24,23), with label word

    (R,A,B,O,A,B), R,A,B,O four distinct actual labels in E.

This is the combinatorial and topological input class. No length
field or geometric realization is assumed here. Repeated visits,
loops, parallel face pairs, distinct-face self-gluings and identical
role words on different owners are allowed under the stated actual
manifold conditions. Numerical equality at distinct labels is allowed.

## 449. Strict angles and a common positive generalized field

The original volume's Theorem 42.2 applies to the manifold, boundary
and original degree hypotheses of Section 448. Starting from the
normalized angles a_o=2/d(P(o)), it preserves every original edge sum
while transporting vertex deficits along the actual boundary-link
surfaces. The total deficit on a link S_nu is

    F_nu-2*V_nu=-2*chi(S_nu)>0.

The theorem makes every angle positive and every local vertex sum
strictly less than pi, while every original edge sum stays 2*pi.
The argument counts source and target occurrences separately even
for self-gluings. It does not assume the unmodified angles already
have strict vertex sums. The constructed angle structure need not
respect equality of a fixed frame's transverse angle pairs; this
is unnecessary at the existence step.

Restore the ideal vertices to the original finite face pairing.
All original faces are paired, so this is the closed triangulated
pseudo 3-manifold used by the hyperideal variational theorem.
Its restored vertices have the prescribed boundary surfaces as
links; truncation recovers N. Closed in this usage does not assert
that the restored quotient is a closed smooth 3-manifold.

The strictly positive angle structure satisfies Luo–Yang's hyperideal
Definition 6.1. Theorem 6.3(a),(c) and Theorem 1.4 provide a volume
maximizer and one common vector ell in R_{>0}^E producing its angles.
Every original edge has angle sum 2*pi, and each owner is genuine
or has two opposite pi angles and four zeros. These are the reused
inputs of the original volume's Corollary 43.1 and Section 285.
The source is Luo–Yang, *Volume and rigidity of hyperbolic polyhedral
3-manifolds*, https://arxiv.org/html/1404.5365v2 .

At this point the field is only generalized: positive coordinates
do not themselves exclude a flat owner. Nor does a strict angle
structure alone ensure that its separate local geometric blocks
have matching lengths. The variational theorem supplies this common
field; no new existence theorem is inferred from flat exclusion.

## 450. Applying the exact flat exclusion to that field

Because the fixed frame uses actual global labels, pulling ell back
to an original tetrahedron gives the length word

    (ell_R,ell_A,ell_B,ell_O,ell_A,ell_B).

Its coshes are greater than one and obey the paired response
formulas. Equality in each repeated pair follows from the common
field, without an averaging operation or additional symmetry.

All original face maps, degrees, label classes and normal intervals
are unchanged. Together with the complete angle sums and positive
length classification, these are precisely the hypotheses of
Section 444. Theorem 447.1 therefore excludes every flat owner.
Consequently ell belongs to the simultaneous genuine length domain
L(T), and all original edge-angle sums are still 2*pi.

The low-sixth and near-maximal cases used in Theorem 447.1 exhaust
1<v<=m only after the exact earlier source reduction. Neither a
local scalar assignment nor the label count alone is substituted
for that reduction in this application.

## 451. The prescribed face gluing and compact completeness

Reuse the cardinality-independent face argument of Section 287.
Each genuine truncated hyperideal tetrahedron has right-angled
hexagonal faces. Across a paired original face, the prescribed
vertex map matches three alternating original-edge sides with the
same lengths ell_e. A right-angled hyperbolic hexagon is determined
by these lengths, so the prescribed side correspondence is realized
by an isometry, with the inverse used on its paired occurrence.
Orientation reversals are kept exactly as prescribed.

The endpoints of each compact side fix its interval isometry;
there is no extra shear parameter. Equal numerical lengths do not
replace the specified map by an arbitrary hexagon symmetry. Thus
the pieces glue using the original face and edge identifications,
including loops and distinct-face self-gluings, and their quotient
is N itself.

At an original interior edge, its connected circular normal link
and total angle 2*pi give a smooth hyperbolic neighborhood without
a cone defect. The actual manifold hypothesis excludes an edge
reversal orbifold. The truncation triangles meet adjacent hexagonal
faces orthogonally, so their planes continue across the seams
without bending. At a boundary-link vertex, its triangle-angle sum
is the original 2*pi edge-end angle sum. Hence the boundary has no
residual cone point and is smooth and totally geodesic.

There are finitely many compact genuine truncated tetrahedra.
Their glued metric on N is compact and therefore complete as an
intrinsic path metric including its boundary. Equivalently, doubling
across the totally geodesic boundary gives a compact smooth closed
hyperbolic manifold. This is not a completeness assertion for the
open interior with the boundary deleted or for a cusp end.

## 452. Realization of the same six-edge triangulation

**Theorem 452.1.** Under exactly the hypotheses of Section 448, the
same original triangulation has a nondegenerate hyperideal
realization with all original edge-angle sums 2*pi and smooth
totally geodesic boundary. Its compact metric on N, including the
boundary, is complete.

Proof. Section 449 supplies a common positive generalized field.
Section 450 makes every owner genuine. Section 451 realizes the
prescribed face pairing and establishes the stated metric and
boundary conclusions.

The strict-angle and variational existence results are reused.
The new input is the completed flat exclusion for exactly six
actual edges and four distinct labels in each fixed paired frame.
The theorem does not cover repeated selected frame labels, six
reservoir labels with additional special actual edges, more than
six actual edges, torus boundary or arbitrary minimum-six-degree
triangulations. No unrestricted CFMP, dynamical convergence,
literature-priority or Lean/kernel verification claim is made.

## 453. A ten-tetrahedron six-edge witness

**Proposition 453.1.** The finite face pairing below gives a connected orientable compact 3-manifold
after ideal-vertex truncation, with one connected genus-5 boundary component,
ten original tetrahedra, and exactly six actual global edges. Their original
degrees are (20,8,8,8,8,8). Every owner has a vertex-induced paired frame with
four distinct labels. Every simultaneous selection of such paired frames has
all six actual labels in its union of transverse labels.

Thus this is a strict separation from the at-most-five-transverse-reservoir
condition, even when the paired frame is allowed to vary on each owner. It is
not a separation claim from every older geometric criterion, a minimality
claim, an unrestricted CFMP result, or a kernel-certified theorem.

The proof is the actual face and interval calculation in Sections 454-457.
No topological property is inferred from an unspecified general family.

## 454. Original labels and all possible paired frames

Use tetrahedra P0,...,P4,M0,...,M4 with vertices 1,2,3,4. Edge order is
(12,13,14,34,24,23). Both copies of each type have this word:

| Type | Label word | Forced transverse pair |
|---|---|---|
| 0 | `(5, 0, 1, 2, 0, 1)` | `{0,1}` |
| 1 | `(1, 0, 2, 3, 0, 2)` | `{0,2}` |
| 2 | `(2, 0, 3, 4, 0, 3)` | `{0,3}` |
| 3 | `(3, 0, 4, 5, 0, 4)` | `{0,4}` |
| 4 | `(4, 0, 5, 1, 0, 5)` | `{0,5}` |

All four selected labels are distinct. Each word has exactly two labels of
multiplicity two and two labels of multiplicity one. In any vertex-induced
paired word, the transverse labels each occur twice, so they must be exactly
the two multiplicity-two labels displayed here. This proves the forced-pair
claim for every possible frame, not just the displayed frame. Their union is
{0,1,2,3,4,5}. Thus allowing any of the 24 vertex permutations on each
owner cannot lower the union of transverse labels.

## 455. All original face pairs and orientations

Fj is the face opposite vertex j. A full permutation q1q2q3q4 sends j to qj;
restrict it to the stated source face. The omitted source vertex is sent to
the omitted target vertex. The inverse map is used in the reverse direction.

| Source | Target | Full vertex map |
|---|---|---|
| P0:F3 | P4:F1 | 3214 |
| P0:F4 | P4:F2 | 1432 |
| M4:F1 | M0:F4 | 4123 |
| M4:F2 | M0:F3 | 2341 |
| P1:F3 | M1:F3 | 1234 |
| P1:F4 | P0:F1 | 2341 |
| M0:F1 | P0:F2 | 2143 |
| M0:F2 | M1:F4 | 1432 |
| P2:F3 | M2:F3 | 1234 |
| P2:F4 | P1:F1 | 2341 |
| M1:F1 | P1:F2 | 2143 |
| M1:F2 | M2:F4 | 1432 |
| P3:F3 | M3:F3 | 1234 |
| P3:F4 | P2:F1 | 2341 |
| M2:F1 | P2:F2 | 2143 |
| M2:F2 | M3:F4 | 1432 |
| P4:F3 | M4:F3 | 1234 |
| P4:F4 | P3:F1 | 2341 |
| M3:F1 | P3:F2 | 2143 |
| M3:F2 | M4:F4 | 1432 |

Every one of the forty original face occurrences appears exactly once.
Substitution in the label table verifies all three edge labels on every
paired face. The involution on face occurrences is fixed-point-free.

Orient every P owner positively in its displayed vertex order and every M
owner negatively. Each listed map satisfies

    sign(target)=-sign(vertex permutation)*sign(source),

so the induced face orientations are reversed. The original dual graph is
connected: the P_i form a chain through the pairs P_i:F4/P_(i-1):F1 for
1<=i<=4, each M_i for i>=1 is attached to P_i, and M0 is attached to P0.
The extra closing pairs do not disturb connectedness or orientation.

## 456. Every oriented original normal circle

A state T:a>b/Ff is an ordered local edge with exiting face Ff. Cross Ff by
its specified face map, carry a and b in their order, and exit by the other
face containing the image edge. The following lists close exactly, including
the ordered endpoints. Each underlying original local edge occurs once in
its displayed cycle.

### Actual edge 0: 20 original intervals

1. `P0:1>3/F2`
2. `M0:2>4/F3`
3. `M4:1>3/F4`
4. `M3:1>3/F4`
5. `M2:1>3/F4`
6. `M1:1>3/F4`
7. `M0:1>3/F4`
8. `M4:2>4/F3`
9. `P4:2>4/F1`
10. `P0:2>4/F1`
11. `P1:1>3/F2`
12. `M1:2>4/F3`
13. `P1:2>4/F1`
14. `P2:1>3/F2`
15. `M2:2>4/F3`
16. `P2:2>4/F1`
17. `P3:1>3/F2`
18. `M3:2>4/F3`
19. `P3:2>4/F1`
20. `P4:1>3/F2`

### Actual edge 1: 8 original intervals

1. `P0:1>4/F2`
2. `M0:2>3/F4`
3. `M4:3>4/F2`
4. `M0:4>1/F2`
5. `M1:2>1/F3`
6. `P1:2>1/F4`
7. `P0:3>2/F4`
8. `P4:3>4/F1`

### Actual edge 2: 8 original intervals

1. `P0:3>4/F1`
2. `P1:2>3/F1`
3. `P2:1>2/F3`
4. `M2:1>2/F4`
5. `M1:1>4/F3`
6. `P1:1>4/F2`
7. `M1:2>3/F4`
8. `M0:4>3/F1`

### Actual edge 3: 8 original intervals

1. `P1:3>4/F1`
2. `P2:2>3/F1`
3. `P3:1>2/F3`
4. `M3:1>2/F4`
5. `M2:1>4/F3`
6. `P2:1>4/F2`
7. `M2:2>3/F4`
8. `M1:4>3/F1`

### Actual edge 4: 8 original intervals

1. `P2:3>4/F1`
2. `P3:2>3/F1`
3. `P4:1>2/F3`
4. `M4:1>2/F4`
5. `M3:1>4/F3`
6. `P3:1>4/F2`
7. `M3:2>3/F4`
8. `M2:4>3/F1`

### Actual edge 5: 8 original intervals

1. `P0:1>2/F3`
2. `P4:3>2/F4`
3. `P3:4>3/F2`
4. `M3:3>4/F2`
5. `M4:3>2/F1`
6. `M0:2>1/F3`
7. `M4:1>4/F3`
8. `P4:1>4/F2`

Each transition is directly obtained from Section 455. Label preservation
prevents different lists from joining; the lists are disjoint and exhaust
all sixty original local edge occurrences. Thus each displayed color is one
actual global edge class, not a union of several unresolved classes. Its
normal quotient is one circle of the displayed degree. The ordered endpoint
return rules out an edge-reversal monodromy. Reversing the orientation gives
the opposite traversal of the same normal circle, not an extra edge class.

## 457. The actual ideal vertex link

Under the face vertex maps, all forty local vertex occurrences belong to one
ideal vertex. The following tree records 39 actual corner identifications
joining them; T:j denotes corner j of owner T. Each row is a restriction
of the indicated face pair in Section 455. Starting at P0:1 and following
the rows reaches every corner occurrence.

| Parent corner | New corner | Source / target faces |
|---|---|---|
| P0:1 | P4:3 | P0:F3 / P4:F1 |
| P0:1 | P4:1 | P0:F4 / P4:F2 |
| P0:1 | M0:2 | P0:F2 / M0:F1 |
| P4:3 | P0:3 | P4:F2 / P0:F4 |
| P4:3 | P3:4 | P4:F4 / P3:F1 |
| P4:1 | M4:1 | P4:F3 / M4:F3 |
| P4:1 | P3:2 | P4:F4 / P3:F1 |
| M0:2 | M4:3 | M0:F4 / M4:F1 |
| P0:3 | P1:2 | P0:F1 / P1:F4 |
| P0:3 | M0:4 | P0:F2 / M0:F1 |
| P3:4 | M3:4 | P3:F3 / M3:F3 |
| P3:4 | M3:3 | P3:F2 / M3:F1 |
| M4:1 | M3:1 | M4:F4 / M3:F2 |
| P3:2 | M3:2 | P3:F3 / M3:F3 |
| P3:2 | P2:3 | P3:F4 / P2:F1 |
| P1:2 | M1:2 | P1:F3 / M1:F3 |
| P1:2 | P2:1 | P1:F1 / P2:F4 |
| M3:4 | P3:3 | M3:F1 / P3:F2 |
| M3:4 | M4:2 | M3:F2 / M4:F4 |
| M3:3 | M2:3 | M3:F4 / M2:F2 |
| M3:1 | P3:1 | M3:F3 / P3:F3 |
| M3:1 | M2:1 | M3:F4 / M2:F2 |
| M3:2 | M2:4 | M3:F4 / M2:F2 |
| P2:3 | P1:4 | P2:F4 / P1:F1 |
| M1:2 | P1:1 | M1:F1 / P1:F2 |
| P2:1 | M2:2 | P2:F2 / M2:F1 |
| P3:3 | P2:4 | P3:F4 / P2:F1 |
| P3:3 | P4:2 | P3:F1 / P4:F4 |
| M4:2 | M0:1 | M4:F1 / M0:F4 |
| M2:3 | M1:3 | M2:F4 / M1:F2 |
| P3:1 | P2:2 | P3:F4 / P2:F1 |
| M2:1 | M1:1 | M2:F4 / M1:F2 |
| P1:4 | M1:4 | P1:F3 / M1:F3 |
| P1:1 | P0:2 | P1:F4 / P0:F1 |
| M0:1 | M4:4 | M0:F3 / M4:F2 |
| M1:3 | M0:3 | M1:F4 / M0:F2 |
| P2:2 | P1:3 | P2:F4 / P1:F1 |
| P0:2 | P4:4 | P0:F4 / P4:F2 |
| M0:3 | P0:4 | M0:F1 / P0:F2 |

The link therefore has forty triangles and is connected by its face-side
gluings. Its 120 triangle sides are paired in sixty
pairs of tetrahedral face corners, giving sixty link edges: equivalently,
3*40/2=60.

Each of the six actual edges has two distinct endpoint classes in this link.
Indeed its ordered normal cycle closes without reversing the ordered edge,
so the two endpoint cycles are separate; no endpoint can change its actual
edge label. Consequently the link has twelve vertices. The original endpoint cycles
account for every link vertex, including the two endpoints of an edge
whose endpoints lie on this same boundary component.

The link of each of these twelve vertices is its original normal cycle,
hence one circle. Together with the complete side pairing, this shows that
the connected link is a closed surface, not merely a two-complex with the
correct Euler number. The orientation established in Section 455 induces an
orientation on this link. Its Euler characteristic is

    chi=12-60+40=-8,

so it has genus five. All other points of the original quotient have the
usual manifold neighborhoods: face interiors are paired in twos, original
edge interiors have the connected circular normal links without reversals,
and tetrahedron interiors are unchanged. Truncating the sole ideal vertex
therefore gives a connected orientable compact 3-manifold with exactly this
closed genus-5 boundary surface. No edge link or ideal vertex is omitted.

## 458. Realization and the limited separation conclusion

The face pairing of Proposition 453.1 meets every hypothesis of Section 448:
there are six actual edges, four distinct labels per fixed paired frame,
original degree at least six, connected normal circles, and one closed
orientable genus-5 boundary link on the connected actual manifold.
Theorem 452.1 therefore realizes this same triangulation by genuine
hyperideal tetrahedra with totally geodesic boundary and a compact complete
metric including that boundary.

The construction has an actual six-label transverse necessity. It cannot
be put into the earlier at-most-five-reservoir class merely by changing
vertex-induced paired frames. This is the asserted strict separation;
it does not exclude another older geometric criterion from proving this
particular triangulation realizable. No minimality or unrestricted CFMP
claim is made, and no explicit numerical edge-length solution is needed
for this application of Theorem 452.1.

## 459. A second strict upper label with repeated frame labels

Consider a finite actual ideal face-pairing quotient with one fixed
vertex-induced paired frame (R,A,B,O,A,B) on each original tetrahedron,
in order (12,13,14,34,24,23), where A and B are distinct actual labels.
The axes R,O may coincide with each other or with either transverse label.
Use a common positive generalized length field and the usual paired-angle
responses. The original Z normal link is a connected circle of degree at
least six. All original face maps and interval endpoints are retained.

Suppose M,Z,C,D are distinct actual labels, with coshes satisfying

    c,d>1, m>=1+c+d, z>=1+m+c,                     (459.1)

and there is a genuine original source

    tau=(Z,M,C,D,M,C).                            (459.2)

Every owner containing a Z slot is genuine. The complete Z-angle sum is
2*pi, and the total genuine M-angle sum is at most pi. Thus the combined
actual genuine M/Z capacity is at most 3*pi. No connectedness or degree
premise for M is needed by this direct argument.

**Theorem 459.1.** These hypotheses are inconsistent with

    x_e<=m for every actual label e different from Z.       (459.3)

No total label count, unique-flat assumption, special-edge barrier or
four-distinct-label condition on general owners enters the direct theorem.
In its application below, the source hypotheses and the wholly genuine
Z star are supplied by existing six-reservoir results, not presumed for
a larger number of reservoirs.

## 460. A three-slot inequality with its exact enlarged other-axis domain

Let m>3, z>m+2, 1<q<=m, and let (M,Z,Q,R,Z,Q) be genuine.
Write w=x_R>1 and assume only

    w<1+z+q.                                      (460.1)

Let theta be the axial M angle and gamma the transverse Z angle.
Then

    theta+2*gamma>pi.                              (460.2)

This extends the scalar estimate of Section 315 of the
[five-reservoir return volume](CFMP_GEOMETRIC_REALIZATION_FIVE_RESERVOIR_RETURN.md)
to the other-axis domain (460.1). In particular (459.3) gives
w<=z<1+z+q, even when R=Z.

Put t=cot(theta/2)>0. The response is

    gamma=atan(A*t)+atan(B*t),
    A=[sqrt(z^2-1)+sqrt(q^2-1)]/(z+q)*sqrt((m-1)/(m+1)),
    B=[sqrt(z^2-1)-sqrt(q^2-1)]/(z+q)*sqrt((m-1)/(m+1)).

Both A and B are positive, since z>m>=q. If q<=m-2, then A+B>1:
compare q with m-2 and z with m; the resulting boundary value is one,
and sqrt(z^2-1)/(z+q) strictly increases with z, its derivative having
positive numerator z*q+1. If gamma>=pi/2 then gamma>atan(t).
Otherwise its tangent is (A+B)*t/(1-A*B*t^2)>t. This proves (460.2)
in the first case with the correct tangent branch.

Now m-2<q<=m. Define k=z+q, h=z-q>0 and alpha=sqrt((m-1)/(m+1)).
The strict genuine factors and response identity are

    L=k^2-(m-1)*(w-1)>0,
    J=(m+1)*(w+1)-h^2>0,
    A+B=2*sqrt(z^2-1)*alpha/k,
    A*B*t^2=(h/k)*(L/J).

Increase the scalar comparison variable w to w0=1+k. Throughout this
path J increases and stays positive. L decreases to

    L0=k*(k-m+1)>0,
    J0=(m+1)*(k+2)-h^2>0.

The endpoint L0 is positive because k>m. The ratio L/J strictly
decreases. The strict assumption (460.1) therefore gives

    A+B+A*B*t^2>F(q),
    F(q)=2*sqrt(z^2-1)*alpha/(z+q)
         +(z-q)*(z+q-m+1)/[(m+1)*(z+q+2)-(z-q)^2].

On q<=v<=m the first term decreases. The second numerator is positive
and has derivative m-1-2*v<3-m<0. Its denominator is positive and has
derivative m+1+2*(z-v)>0. Hence F(q)>=F(m). At m,

    J0(m)=(z+1)*(3*m+2-z)>0,
    F(m)=2*sqrt(z^2-1)*alpha/(z+m)+(z-m)/(3*m+2-z).

Thus z<3*m+2. Both terms in F(m) strictly increase with z on
m+2<=z<3*m+2: the derivative numerators have signs m*z+1>0 and
2*m+2>0, respectively. Since z>m+2,

    F(m)>sqrt(1-4/(m+1)^2)+1/m>1.

For the last comparison, both 1-1/m and the square root are positive;
the squared difference has positive numerator

    (2*m-1)*(m+1)^2-4*m^2
      =(m-1)*(2*m^2+m+1)>0.

Consequently A+B+A*B*t^2>1. When gamma<pi/2, its positive tangent
is greater than t; when gamma>=pi/2, gamma>atan(t) directly. In either
case gamma>atan(t)=(pi-theta)/2, proving (460.2). No angle expense is
asserted monotone in w; only the displayed rational ratio is compared.

## 461. The source axial run has exactly one original interval

Assume (459.3). From (459.1), m>3, c<m-2, z>m+2 and z-1>=m+c.
On the maximal axial Z run through tau, the fixed pair is {M,C}.
All its owners are genuine. No such owner has two axial Z slots:
that would give L=(m+c)^2-(z-1)^2<=0. Thus the original intervals
of this run have distinct owners.

For each of them the individual transverse M response has two
positive arctangent coefficients whose sum is

    2*sqrt(m^2-1)/(m+c)*sqrt((z-1)/(z+1))>1.

Indeed compare c with m-2 and z with m; equality would hold at those
boundary values, while the actual inequalities are strict. The same
tangent-branch argument as in Section 460 gives

    theta_Z+2*beta_M>pi.                           (461.1)

If the entire Z circle were axial, it would have at least six such
original intervals and exceed the available 3*pi M/Z capacity. So
the run is proper. Its two original transverse boundary Z intervals
are distinct: otherwise that one interval and the run would close the
whole circle, leaving the other transverse Z slot of its owner outside.
Their owners have the form

    (B,Z,A,Q,Z,A), {A,B}={M,C}.

Write a=x_A,b=x_B,q=x_Q. By (459.3), q<=z<1+z+a. The transverse Z
cosine numerator is increasing in q, with derivative a+z*b>0, and
at q=1+z+a it is

    [a+z*(1+z+a)]*(1+a+b-z)<=0.

Therefore each boundary Z angle is strictly greater than pi/2.
Every such owner has two equal transverse Z slots. Two different
boundary owners would already use more than 2*pi at Z, so both
boundary intervals belong to one actual owner rho. Its two
transverse Z angles alone use more than pi.

Together with (461.1) and the total 3*pi capacity, this forces the
axial run to have exactly one owner, tau. No distinctness of other
axes was used. The two possible rho frames are

    (M,Z,C,Q,Z,C), or (C,Z,M,Q,Z,M).                (461.2)

## 462. The repeated-Z companion-C return closes four intervals

In the first case of (461.2), genuineness gives

    (m+1)*(q+1)>(z-c)^2>=(m+1)^2.

Thus q>m, and (459.3) forces Q=Z. So

    rho=(M,Z,C,Z,Z,C).

For any genuine owner with pair {Z,C}, if at least one axis is not
Z, its value b<=m and the other axis has value r<=z. The same increasing
cosine-numerator comparison at r0=1+z+c is nonpositive because
z>=1+m+c>=1+b+c; the actual r<r0 makes it strictly negative.
Its two transverse Z angles are therefore obtuse. Since rho already
has two such angles, no second owner of this kind is possible.

The remaining possible pair-{Z,C} owner has both axes Z. Its four
Z slots have the same cosine

    z*(c+1)/(2*z^2+c-1)<1/2,

because z>c+1. Their expense is greater than 4*pi/3 and cannot
coexist with rho's Z expense greater than pi. Hence rho is the
unique actual owner with pair {Z,C}.

Its two faces at its sole M axis are paired to the two faces at
tau's axial Z interval. The remaining rho faces have multiset
{Z,Z,C}. Follow a transported Z slot across either. If it is axial,
the complementary labels force pair {Z,C}. If it is transverse,
its companion cannot be Z because transverse labels are distinct;
it is C and the other Z on the face is axial. Again its pair is
{Z,C}, hence its owner is rho. This includes either image of a Z
slot under a label-preserving face permutation.

Thus the one Z interval of tau and three Z intervals of rho form
a nonempty closed union of original normal intervals. Connectedness
makes it the whole Z circle, of degree at most four, contradicting
degree(Z)>=6. Distinct-face self-gluings and edge-orientation reversals
in individual maps only change the endpoint matching inside this
closed set; no distinct-neighbor assumption was introduced. If such a
matching splits the closed set into multiple circular components, it
already contradicts connectedness. Otherwise the degree bound excludes
the single component. Interval interiors are never identified by a
face map, so repeated labels do not erase original intervals.

## 463. The companion-M return is the only owner of its fixed pair

Only the second case of (461.2) remains:

    rho=(C,Z,M,Q,Z,M).

Its genuine inequality and (459.1) give

    (c+1)*(q+1)>(z-m)^2>=(c+1)^2,

so q>c and Q!=C. Both tau and rho contain C and each spends more
than pi of genuine M/Z capacity. A genuine owner whose labels were
all in {M,Z} would be different from both and would spend more than
pi of M/Z itself, which is impossible.

The latter is the two-value estimate of Section 157 of the
[paired-reservoir volume](CFMP_GEOMETRIC_REALIZATION_TWO_RESERVOIRS.md),
which allows repeated axes. Its application here is as follows.
Every local cosh is >3.
At each vertex its axial angle theta and the two transverse angles
have sum theta+2*atan(lambda*cot(theta/2)), where 1>lambda>2/3.
For t=tan(theta/2)>0, tangent addition and AM-GM give

    atan(t)+atan(lambda/t)>=2*atan(sqrt(lambda)),

with both sides in (0,pi/2). The vertex sum is at least
4*atan(sqrt(lambda))>pi/2. Summing the four vertices counts every
angle twice, giving six-angle total >pi.

Now any pair-{Z,M} owner must have at least one axis B outside M,Z,
with b<=m; its other axis has value r<=z. It is genuine since it
contains Z. Put

    L=(z+m)^2-(b-1)*(r-1)>0,
    J=(b+1)*(r+1)-(z-m)^2>0.

Monotonicity of the following polynomial in b,r yields

    L-2*J=3*z^2-2*z*m+3*m^2-3*b*r-b-r-3
         >=3*z^2-5*z*m+3*m^2-m-z-3
         =(m-3)*(m+1)+(z-m)*(m-1)+3*(z-m)^2>0.

Both b and r are positive; each partial derivative of the subtracted
part is negative. The last expression is positive for m>3 and z>m.
The squared paired coefficient

    K=[(sqrt(z^2-1)+sqrt(m^2-1))/(z+m)]^2>8/9

therefore satisfies K*L/J>16/9>1. The response

    beta_Z+beta_M=2*atan(sqrt(K*L/J))>pi/2

shows that the four transverse M/Z slots spend more than pi.
Two such owners together with tau would exceed 3*pi. Thus rho is
the unique actual owner of pair {Z,M}, even with repeated axes.
All owners other than tau,rho have combined M/Z capacity below pi.

## 464. Repeated opposite labels close at most four intervals

If Q=M, the unused rho faces have multiset {Z,M,M}. A transported
Z slot cannot become axial, since that would require two identical
transverse labels M,M. If transverse it has pair {Z,M}, hence owner
rho. The tau interval and rho's two Z intervals are closed, so the
connected Z circle has at most three intervals, impossible.

If Q=Z, the unused faces have multiset {Z,Z,M}. A transported Z slot
is either axial with pair {Z,M} or transverse with companion M;
companion Z is forbidden. Both cases return to rho. Its extra axial
Z interval is included, so tau and rho close at most four original
Z intervals, again impossible.

Consequently Q is distinct from M,Z,C. Its value still satisfies
1<q<=m. This conclusion is derived; four-distinctness of rho was
not an input.

## 465. The residual run is charged by original intervals, not owners

The unused rho faces now have three distinct labels {Z,M,Q}. A
transported Z slot is exactly one of these roles:

1. axial, with fixed pair {M,Q};
2. transverse, with pair {Z,M}, hence belonging to rho;
3. transverse, with pair {Z,Q} and an M axis, in a frame
   eta=(M,Z,Q,R,Z,Q).

The third owner is genuine, differs from tau and rho by its fixed
pair, and has x_R<=z<1+z+q. Section 460 gives its three-slot M/Z
expense >pi, contrary to the remaining capacity below pi. Thus
no third-role owner occurs.

The tau interval is one axial {M,C} arc between rho's two transverse
Z intervals. The complementary arc contains every other Z interval.
Starting at either residual rho face and using the displayed role
list, original face transport preserves pair {M,Q} until a transverse
boundary. The only permitted transverse boundary is rho itself.
The complementary arc is therefore one axial {M,Q} run with

    n=degree(Z)-3>=3

original intervals. An immediate return would leave no such remaining
intervals and is equally excluded by connectedness and the degree.

For any axial Z slot of this run, let theta be its angle and beta
its owner's transverse M angle. Its exact response is

    beta=atan(A*t)+atan(B*t), t=cot(theta/2)>0,
    A=[sqrt(m^2-1)+sqrt(q^2-1)]/(m+q)*sqrt((z-1)/(z+1)),
    B=[sqrt(m^2-1)-sqrt(q^2-1)]/(m+q)*sqrt((z-1)/(z+1))>=0.

Let alpha=sqrt((m-1)/(m+1)) and s=sqrt((z-1)/(z+1)). Since q>1,

    sqrt(q^2-1)>alpha*(q-1),
    sqrt(m^2-1)=alpha*(m+1),

so A>alpha*s>1/2 because m,z>3. If theta>=pi/2, then theta+beta>pi/2.
Otherwise t>1 and cot(theta)=(t-1/t)/2<t/2<A*t, giving the same
strict conclusion.

An owner in this run can supply one or two axial Z intervals. It
has exactly two transverse M slots. Assign one beta to each original
axial Z interval. With one Z axis this uses one of those two M slots;
with two Z axes the equal-axis symmetry gives their equal responses
and the two assigned betas are exactly the two actual transverse M
angles. Extra axial M slots, if present, are not charged. Every run
owner differs from tau,rho by its fixed pair, and no actual angle
is charged more often than its original multiplicity.

The resulting actual M/Z expense is greater than n*pi/2>=3*pi/2.
But these owners have remaining capacity below pi. This contradiction
completes the direct theorem, preserving repeated intervals, repeated
owners, loops, parallel face pairs and distinct-face self-gluings.

## 466. Exact six-edge consequence and what is still missing

Retain the paired-framework hypotheses of Section 130 of the
[paired-reservoir volume](CFMP_GEOMETRIC_REALIZATION_TWO_RESERVOIRS.md)
in its inherited manifold class: a connected orientable compact
3-manifold with nonempty boundary consisting of closed surfaces of
genus at least two, given by an actual finite ideal tetrahedron pairing.
The face pairing is a fixed-point-free involution on original face
occurrences, each actual edge normal link is one connected circle,
and every original edge degree is at least six. Take H=E with exactly
six actual global edge labels and no special labels. Each original
owner has a fixed vertex-induced frame (R,A,B,O,A,B), with A!=B;
repetitions among R,A,B,O are permitted. Use one common positive
generalized length field satisfying all original angle equations 2*pi,
and suppose that its flat set is nonempty.

**Corollary 466.1.** If M is a maximal-valued label selected by a flat
pi slot and Z is the upper label in its source reduction of Sections
132-134, there is a second actual label U distinct from Z with u>m.
In particular M,Z,C,D,U are five distinct actual labels.

**Proof.** Sections 132-134 supply M,Z,C,D,tau and (459.1), with
p_M=1 and p_Z=0. Sections 304-307 of the five-reservoir return volume
make every actual label genuinely witnessed and every
flat axial-selected. The arbitrary upper-witness theorem excludes flat
transverse Z occurrences, since z>m-2. Axial Z cannot be flat either,
because p_Z=0 and every flat selects its axes. Thus its entire star
is genuine. Its complete angle budget is 2*pi, and the genuine M
budget is pi. All hypotheses of the direct theorem hold if every
label other than Z is at most m, so that supposition is impossible.

Therefore some actual label U different from Z satisfies u>m.
It differs from M,C,D as well because c,d<m-2. This is the
second-upper-label conclusion of Sections 314-316
with repeated axes allowed. It does not assert the further source-pair
conclusions of Section 317. QED.

In particular the source flat's other axis is no longer automatically
the sixth label V: it may coincide with C or D. Its repetition of M
is impossible because that would use two M pi slots, but repetition
of a transverse C or D is not excluded by this proof. The at-most-two-flat
theorem of Sections 309-313 of the five-reservoir return volume still
applies; unique flatness and uniqueness of a CD-pair owner do not yet follow. The
360-word census and subsequent six-edge closure cannot simply be
reused for these repeated-label owners.

For seven reservoirs, Sections 304-307 and the at-most-two-flat theorem
do not apply: two reservoir labels may remain unwitnessed after the
arbitrary upper-witness step. A high label can then have axial flat
zero slots. The hypotheses above do not supply a wholly genuine Z star
in that setting. For six reservoirs plus special actual edges, the
hypothesis (459.3) bounds all actual values, including special axes;
no such bound is silently inferred from a bound on reservoirs only.
Thus Theorem 459.1 and Corollary 466.1 give no flat-exclusion or
realization conclusion for either of these larger classes.

## 467. A source-specific maximum bound with repeated axes

Use a finite actual ideal face-pairing quotient. Every original tetrahedron
has one fixed vertex-induced frame (R,A,B,O,A,B), in edge order
(12,13,14,34,24,23), with distinct actual transverse labels A,B. Axes
may repeat each other or transverse labels. The original face pairing
is a fixed-point-free involution on original face occurrences. Retain
its vertex maps and every original normal interval.
A common positive generalized length field supplies the usual paired
responses. Let M,Z,C,D be four distinct actual labels with

    c,d>1, m>=1+c+d, z>=1+m+c,
    tau=(Z,M,C,D,M,C) genuine.

Every owner containing Z is genuine. Its complete original Z-angle sum
is 2*pi and its normal link is one connected circle of original degree
at least six. The total genuine M-angle expense is at most pi. Thus
actual genuine M/Z expense is at most 3*pi. Define

    w=max{x_e : e is an actual label different from Z}.

This maximum exists because the actual edge set is finite and contains
M,C,D. In particular w>=m>3. No label-count, unique-flat, special-edge
barrier, four-distinct-frame or degree condition for M is imposed.

**Theorem 467.1.** Under these hypotheses,

    z<1+2*w.                                           (467.1)

This is a source-specific bound. It is not the four-distinct gap
z<u+m+1, and does not identify w with a prescribed label U.
It does not resolve the source-axis C/D cases or exclude a second flat.

The proof uses the paired cosine and genuine-factor formulas of
Sections 95 and 130 of the
[paired-reservoir volume](CFMP_GEOMETRIC_REALIZATION_TWO_RESERVOIRS.md),
and the source charge from Section 461. All interval counts below
are original multiplicities, even when two slots have the same label.

## 468. Every transverse Z owner has three or four Z slots

Suppose instead z>=1+2*w. Then z>w. Consider any owner with transverse
pair {Z,A}, where a<=w and A!=Z. Its two axes have values b,r.

If neither axis is Z, both b,r<=w. Its genuine inequality would require

    (b+1)*(r+1)>(z-a)^2,

whereas z-a>=1+w and (b+1)*(r+1)<=(w+1)^2. This is impossible.
Thus at least one axis is Z.

If one axis is not Z, name it B, with b<=w; its other axis is Z.
The transverse Z cosine has a positive denominator and numerator

    N(r)=a*(b+r)+z*(b*r+a^2-z^2+1).

Its derivative in r is a+z*b>0. At the algebraic comparison value
r0=1+z+a it factors as

    N(r0)=[a+z*(1+z+a)]*(1+a+b-z)<=0,

because a+b<=2*w<=z-1. The actual r=z is strictly below r0, so
N(z)<0. Each of its two equal transverse Z angles exceeds pi/2.
The owner has exactly three original Z slots, and its total Z
expense is greater than pi. No genuine test at r0 is needed here.

If both axes are Z, its frame is (Z,Z,A,Z,Z,A). All four original
Z angles have the same cosine

    z*(a+1)/(2*z^2+a-1)<1/2.

Indeed z>a+1, and cross multiplication leaves
2*z*(z-a-1)+a-1>0. Thus this four-slot owner spends more than 4*pi/3
at Z, and in particular more than pi.

Every transverse Z owner therefore spends more than pi at Z.
The complete Z equation permits at most one such actual owner, rho.
This counts all its axial and transverse Z slots; repeated labels
are not collapsed to one angle.

## 469. The source axial charge and existence of rho

The source inequalities imply m>3, c<m-2 and z>m+2. For any genuine
axial Z occurrence with fixed pair {M,C}, let theta be the Z angle,
beta its transverse M angle and t=cot(theta/2)>0. The exact response is

    beta=atan(A*t)+atan(B*t),
    A=[sqrt(m^2-1)+sqrt(c^2-1)]/(m+c)*sqrt((z-1)/(z+1)),
    B=[sqrt(m^2-1)-sqrt(c^2-1)]/(m+c)*sqrt((z-1)/(z+1)).

Both coefficients are positive, and

    A+B=2*sqrt(m^2-1)/(m+c)*sqrt((z-1)/(z+1))>1.

To verify the strict comparison, replacing c by m-2 and z by m
would give one; the actual c is smaller and z is larger. If beta
is at least pi/2 then beta>atan(t). Otherwise its positive tangent
is (A+B)*t/(1-A*B*t^2)>t. In either branch,

    theta+2*beta>pi.                                  (469.1)

No genuine owner of pair {M,C} can have two axial Z slots, since
its first genuine factor would be

    (m+c)^2-(z-1)^2<=0.

If the whole original Z circle were axial, actual face transport
would preserve the fixed pair {M,C} through tau around the circle.
All its intervals would have distinct owners by the preceding factor.
Summing (469.1) over at least six intervals uses distinct original M/Z
angles and contradicts their total capacity 3*pi. Thus there is a
transverse Z occurrence, and rho is the unique owner of all such
occurrences. Tau is different from rho, since its fixed transverse
pair is {M,C}, not a pair containing Z.

## 470. The four-slot owner closes the entire Z circle

Suppose rho has both axes Z. Every original face of rho has multiset
{Z,Z,A}. Follow either tracked Z edge across any such face. If its
image is axial, the other two edge labels force fixed pair {Z,A}.
If its image is transverse, its companion must be A: companion Z
would violate distinctness of the transverse labels. It again belongs
to a pair-{Z,A} owner. Every such owner is a transverse Z owner,
hence is rho itself.

Consequently every endpoint of rho's four original Z normal intervals
is paired inside those four intervals. They form a nonempty closed
subcollection. If it splits into more than one circular component,
connectedness is already violated. If it has one component, that is
the entire connected actual Z circle and has degree four. Both
possibilities contradict the required connected degree at least six.
This includes self-gluings and every orientation of the original maps.

## 471. The three-slot owner: the two exact face-map alternatives

The remaining case has fixed frame

    rho=(B,Z,A,Z,Z,A), B!=Z, A!=Z.

Its Z slots are edges 13,24,34. The two original faces 134 and 234
have multiset {Z,Z,A}; the other two faces have multiset {B,Z,A}.
The preceding receiving-role argument forces both {Z,Z,A} faces to
pair within rho. Since B!=Z, they are exactly rho's two such faces,
so the original fixed-point-free face involution pairs them to each
other. They cannot pair to one and the same original face.

There are precisely two label-preserving vertex maps from 134 to 234.
The unique A edge 14 must map to 23, while the common vertex 3 of
the two Z edges must map to vertex 4. Thus the maps, written by the
images of (1,3,4), are

    (2,4,3), or (3,4,2).                            (471.1)

For the first map, edge 34 maps to itself with reversed endpoint
order. Its one original normal interval has its two endpoints paired
to each other. It is a closed one-interval component, impossible in
a connected original circle of degree at least six. The other two
Z intervals do not erase this component.

For the second map, edge 13 maps to 34 and edge 34 maps to 24.
The three original Z intervals form one path, in order 13,34,24,
whose two external endpoints lie on the remaining faces 123 and 124.
Reversing the face-map direction merely reverses this path. No
interval interior is identified, and all three intervals remain
original occurrences of rho.

## 472. The complementary source run exceeds the actual capacity

In the second alternative, the connected normal circle consists of
this three-interval rho path and its complementary arc. The latter
contains every other original Z interval, including tau. It has

    n=degree(Z)-3>=3

intervals. All are axial, because rho is the only transverse Z owner.
Actual face transport along this axial arc preserves its pair; since
it contains tau, that pair is {M,C}. In particular the complementary
pair at either residual rho face, {A,B}, must equal {M,C}. If A=B,
an axial receiver would be impossible and no complementary arc of
positive length could exist; that case is excluded by the same degree
and connectedness hypotheses, rather than by a frame assumption.

Each owner along this complementary arc has exactly one Z occurrence:
there is no transverse Z owner other than rho, and two axial Z slots
with pair {M,C} fail the genuine factor in Section 469. Hence these n
intervals have distinct actual owners, each different from rho, and
the two transverse M angles charged in (469.1) are distinct original
slots. Summing gives actual genuine M/Z expense strictly greater than
n*pi>=3*pi, contradicting the total capacity at most 3*pi. No expense
from rho is needed for this last strict contradiction.

This proves (467.1). Every count is by original slots and intervals;
loops, parallel face pairs, repeated labels, repeated visits and
individual face-map orientation reversals are retained.

## 473. Exact six-actual-edge application

Retain the full manifold, face-involution, fixed-frame and original-degree
hypotheses of Section 466. In this class, take exactly six
actual reservoir labels, distinct transverse labels per fixed frame,
and allow repeated axes. Assume the given common positive generalized
field has a nonempty flat set. The source and six-reservoir witness
reductions supply all premises of Theorem 467.1, so (467.1) holds for
its designated source label Z. Corollary 466.1 additionally gives
at least one U!=Z with u>m; the maximum w is therefore greater than m.

The bound is z<1+2*max_{e!=Z}x_e. It does not order the extra label V,
replace w by a chosen U without a separate maximum premise, or give
the one-sided bound z<u+m+1 needed in the older four-distinct analysis.
The repeated source-axis C/D and possible two-flat cases remain open.

## 474. A stronger lower source gap when C is the repeated axis

Use common positive cosh lengths for four distinct labels M,Z,C,D,
with m>=1+c+d, z>=1+m+c and c,d>1. Let

    tau=(Z,M,C,D,M,C)

be genuine, and suppose its two original transverse M angles together
spend at most pi. No degree or face-incidence hypothesis is used below.

**Proposition 474.1.** If the source flat is

    sigma=(M,C,D,C,C,D),

selecting its two axial occurrences, then z>2*m+1.

**Proof.** Its axial-flat inequality is

    (m-1)*(c-1)>=(c+d)^2.

The polynomial division identity

    (c+d)^2=(c-1)*(c+2*d+1)+(d+1)^2

therefore gives

    m>=c+2*d+2+(d+1)^2/(c-1)>c+2*d+2.

Put t=m-c-2*d-2>0. The transverse M cosine numerator in tau is

    N(z)=c*(z+d)+m*(z*d+c^2-m^2+1).

Its denominator is positive. The two equal M angles fit at most pi,
so each is at most pi/2 and N(z)>=0. Also N is strictly increasing
in z, with derivative c+m*d>0. Direct substitution gives

    -N(2*m+1)
      =t^3+(3*c+4*d+6)*t^2
       +(2*c^2+8*c*d+10*c+4*d^2+15*d+11)*t
       +2*(d+1)*(c^2+2*c*d+3*c+3*d+3)>0.

Consequently N(z)>=0 requires z>2*m+1.

If the hypotheses of Theorem 467.1 also hold, including the connected
original circle and complete budgets, then z<1+2*w for
w=max_{e!=Z}x_e. Combining the inequalities gives w>m.
This is only a quantitative consequence in this repeated-C source case;
it does not exclude that source or replace Corollary 466.1. QED.

## 475. Repetition of D does not imply the same local source gap

**Proposition 475.1.** The exact tuple

    (m,c,d,z)=(100,2,90,112)

defines an axial-flat local word sigma=(M,C,D,D,C,D), a genuine
local word tau with transverse M expense less than pi, and z<2*m+1,
despite both weak source inequalities.

**Proof.** Its axial-flat product is

    (m-1)*(d-1)=8811>8464=(c+d)^2.

It satisfies m>=1+c+d and z>=1+m+c. The source tau is strictly
genuine because its two paired genuine factors are

    L=(m+c)^2-(z-1)*(d-1)=525>0,
    J=(z+1)*(d+1)-(m-c)^2=679>0.

Its transverse M cosine numerator is N(z)=8904>0, so its two M
angles spend strictly less than pi. Yet z=112<201=2*m+1.
Thus the local hypotheses in Section 474, with C repetition replaced
by D repetition, do not imply the same source gap. This exact tuple
is a scalar counterexample to that substituted implication; it is
not an actual complete face quotient or a flat-exclusion counterexample. QED.

## Continuation: repeated-axis two-flat obstructions

The [repeated-axis continuation](CFMP_GEOMETRIC_REALIZATION_SIX_EDGE_REPEATED_AXES.md)
gives the exact six two-flat role cases and excludes v>m-2 in the stated
two-flat, six-actual-edge repeated-frame branch. The one-flat and
v<=m-2 two-flat branches remain open.
