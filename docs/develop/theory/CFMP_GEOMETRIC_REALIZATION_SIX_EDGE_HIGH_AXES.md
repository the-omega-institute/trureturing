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
