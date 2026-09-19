[Index](../marked_head_profile.md) · [Complete K-face source geometry](75-forced27-and-complete-pure3-deletion-on-the-k-faces.md) · [Common surviving source tables](83-common-seven-hinges-on-both-complete-k-control-faces.md) · [Current complete comparison](104-one-test-layout-couples-the-hinges-of-each-complete-cost.md)

# A complete second-factorial tail improves four quadratic costs

On both complete actual saturated K-control beta faces, every complete
independently labelled357 test A satisfies

    T5(A):=sum_(j>=5)integral(A-j)_+ dmu
          =(1/2)*integral(A-5)_+*(A-4) dmu
          <=619/720.                             (FT0)

All original residues and exponent tails are retained. The proof
controls the desired factorial tail directly and repartitions an
explicit nonnegative LCM-cap series. It does not subtract upper hinge
bounds from an unknown square moment.

Against the current104 cost rows, this improves four of the five
quadratic costs. The tuple00 row retains its stronger existing bound.
With every other cost and101's complete denominator retained, the
resulting full face comparison is

    N<=35.164365148791272560864459998102...,
    d>=1358432973299/17084377926000,
    C0+N/d<=463.8399481443276164982529989299... .    (FT1)

The decrease from104 is0.2599516955287306266284429742.... The scope
is r=rho=0 and D=53/360 on the two entire actual faces
(398,410,422),(1,1) and(616,628,640),(1,0). The comparison remains
above403. This is an ordinary exact-arithmetic result, with no
off-face extension, new global K, Lean verification or unrestricted
Erdos #7 resolution.

## 1. Split the factorial tail before bounding any moments

Keep the six original zero-seven head indicators

    B=I1+I3+I9+I5+I15+I45, I1=1,

and write A=B+R. The tail labels partition into O, all remaining
zero-seven labels, and S7, all positive-seven labels. Put

    Phi(n)=(n-5)_+*(n-4)/2,
    h4(n)=(n-4)_+.

For nonnegative integers b,t,

    Phi(b+t)<=Phi(b)+h4(b)*t+t*(t-1)/2.           (FT2)

When b>=4 this is the quadratic identity, including b=4. When b<=3,
Phi(b)=h4(b)=0 and (b+t-4)_+<=t, so its binomial coefficient is at
most t*(t-1)/2. Apply(FT2) to B,R and expand the last term into
unordered pairs of distinct original tail labels. This gives

    T5<=H+C_old+C_7+P_TT,
    H=integral Phi(B) dmu,
    C_old=sum_(q in O)integral h4(B)*I_q dmu,
    C_7=sum_(q in S7)integral h4(B)*I_q dmu,
    P_TT=sum_({q,q'} subset O union S7)mu(I_q*I_q').
                                                   (FT3)

For infinite families, first use finite label sets containing the
head. The positive terms increase to the displayed quantities, and
the complete bounds below are finite. Monotone convergence therefore
gives(FT3) without a tail cutoff.

Since1<=B<=6, Phi(B) is1 only when all six indicators occur. That
event is contained in the45-test. The whole K-face cap of75 gives

    H<=4/225.                                    (FT4)

## 2. One complete old-tail operator retains the head layout

Use83's canonical first-beta cell2 source tables, indexed by ternary
cell c and five-slot s. Let eta=(1/18,1/9,1/9,1/9,1/9), and write

    p(c,s)=(0, 1/5 if c<2 else0,
               0 if c=2 else1/5,
               3/20 if c<2 else1/10, 1/5),

    w(c,s)=1-[I_(c>=2)+I_(c=1)+I_(s=4)
                                      +I_(c>=2,s=4)]/5,

    d(c,s)=0 if s=0 or(s=1,c>=2)or(s=2,c=2),
           eta_c otherwise.

The surviving measure is bounded by w times the actual source.
These tables retain the first-beta zero slot and allow all remaining
beta mass to be distributed over its whole face. They are the K-face
tables of75 and83, not the separate J-control geometry.

For a fixed independent six-head layout

    ell=(r3,c9,s5,r15,s15,c45,s45),

the head load is

    B_ell(c,s)=1+I_(ROOT(c)=r3)+I_(c=c9)+I_(s=s5)
                  +I_(ROOT(c)=r15,s=s15)+I_(c=c45,s=s45).

Set z(c,s)=w(c,s)*h4(B_ell(c,s)). The five disjoint complete old-tail
categories give the positive operator

    O(z)=(1/18)*max_c sum_s p(c,s)*z(c,s)
        +(1/20)*max_s sum_c d(c,s)*z(c,s)
        +(1/20)*max_(r,s)sum_(ROOT(c)=r)d(c,s)*z(c,s)
        +(1/20)*max_(c,s)d(c,s)*z(c,s)
        +(1/72)*max_(c,s)z(c,s).                  (FT5)

They are, respectively, pure3 depths a>=3; pure5 depths b>=2;
3*5^b;9*5^b; and a>=3,b>=1 mixed labels. The coefficients are the
complete sums

    sum_(a>=3)3^-a=1/18,
    sum_(b>=2)5^-b=1/20,
    sum_(a>=3,b>=1)3^-a*5^-b=1/72.

Each original residue is bounded separately in its category. The
nonnegative objective z already contains the surviving weight w
once; no deletion credit is subtracted a second time. Thus

    C_old<=max_ell O(w*h4(B_ell))=1/15.           (FT6)

The checker enumerates all12500 independent six-head layouts using
integer scaling. One maximizing layout is(0,0,1,0,1,0,1); its five
contributions are1/45,1/180,1/180,1/180,1/36. Their sum is1/15.
This is a maximum of an upper-bound operator, not an assertion that
an actual source or covering family attains it.

First-beta cell permutations2,3,4 preserve the source tables,
ROOT groups and the complete layout set. Exchanging root0 cells0,1
transports the source and test labels to the second K face. Hence
(FT6) holds on both entire actual faces without interpolation of
separately optimized vertex values.

## 3. The positive-seven cross term uses a complete raw45 row

Write N=I3+I9+I5+I15+I45. The elementary indicator inequality is

    h4(B)=(N-3)_+<=I45+I3*I9*I5*I15.             (FT7)

For N<=3 the left side is zero. For N=4, either I45 occurs or the
other four indicators all occur. For N=5, both terms on the right
are1.

For each positive-seven label3^a*5^b*7^e, either intersection in
(FT7) is empty or its old-coordinate part lies in an LCM cylinder
of depth(max(2,a),max(1,b)). The four-indicator intersection is a
45-cylinder only when the original residues are compatible; this
does not identify any independent residues.

Let c_raw(a,b) be the K-face raw cylinder cap of84's complete square
calculation. Its complete45 row is

    S_raw(45)=sum_(a,b>=0)c_raw(max(2,a),max(1,b))
       =2/15+1/45+1/60+1/360=7/40.              (FT8)

The four terms partition the exponent regions a<=2,b<=1;
a>=3,b<=1; a<=2,b>=2; a>=3,b>=2. The complete positive-seven
factor is sum_(e>=1)6/(5*7^e)=1/5. There are two terms in(FT7), so

    C_7<=2*(1/5)*(7/40)=7/100.                  (FT9)

## 4. Repartition the cap series, including its diagonal

Let c0(a,b) denote75's surviving arbitrary-cylinder cap. The pair
majorant uses c0 when both labels have seven exponent zero, and
6/(5*7^e) times c_raw at the old-coordinate LCM when their maximum
seven exponent is e>=1. These are the termwise K-face caps of
`k_face_complete_ratio.py`. Their ordered complete pair series is

    Q_cap=4651/1800+(2/3)*(173/48)=374/75.         (FT10)

For a head label h, let S0(h) and Sraw(h) be its complete rows
against all old zero-seven exponents, using c0 and c_raw respectively.
Its row against the entire357 family is S(h)=S0(h)+Sraw(h)/5:

| h | S0(h) | Sraw(h) | S(h) |
| --- | ---: | ---: | ---: |
| 1 | 73/150 | 55/72 | 1151/1800 |
| 3 | 691/1800 | 11/18 | 911/1800 |
| 9 | 103/360 | 7/18 | 131/360 |
| 5 | 529/1800 | 9/20 | 691/1800 |
| 15 | 421/1800 | 3/8 | 139/450 |
| 45 | 29/200 | 7/40 | 9/50 |

Every row is summed over the four complete exponent regions used
in(FT8). The checker also independently reconstructs it from each
of two finite rectangles plus its entire infinite complement.

The sum of these rows is536/225. The ordered head-head cap sum is
859/600. Therefore the ordered tail-tail cap subseries is exactly

    Q_TT=374/75-2*(536/225)+859/600=2977/1800.     (FT11)

The full diagonal cap series is1151/1800, and the head diagonal
is713/1800. The tail diagonal is thus73/300. Removing it from
the ordered tail-tail series and dividing by2 gives

    P_TT<=((2977/1800)-(73/300))/2=2539/3600.     (FT12)

These subtractions are identities between known nonnegative cap
subseries. No unknown actual moment is being reduced by an upper
bound. An independent disjoint partition in the checker confirms
the same value: the ordered O-by-O cap is107/300, the O-by-S7 cap
in one orientation is121/720, and the ordered S7-by-S7 cap is173/180.
Their diagonal parts are163/1800 and11/72. The complete factor for
two positive-seven exponents is

    sum_(e>=1)(2e-1)*6/(5*7^e)=4/15,

so the latter block is(4/15)*(173/48). This retains the complete
old-old, old-seven and seven-seven complements separately.

Combining(FT4),(FT6),(FT9),(FT12) proves

    T5<=4/225+1/15+7/100+2539/3600=619/720.

## 5. The full quadratic tail changes four current rows

For each of the five original quadratic AP costs f, let

    d1=f(2)-f(1),
    kappa_j=f(j+1)-2*f(j)+f(j-1), j=2,3,4,
    theta=2 times its complete quadratic leading coefficient.

All these coefficients are nonnegative, f(1)=0, and the exact
all-load expansion is

    f(v)=d1*(v-1)+sum_(j=2..4)kappa_j*(v-j)_+
                                  +theta*Phi(v). (FT13)

The polynomial tail is valid from load4. The checker verifies every
low-load transition and matches all polynomial coefficients beyond
that cutoff, so(FT13) does not truncate the quadratic cost tail.
Using104's retained hinge bounds U1,...,U4 gives

    integral f(A)dmu
       <=d1*U1+sum_(j=2..4)kappa_j*Uj
                                      +theta*(619/720). (FT14)

The current-row comparison is:

| Tuple | Current104 upper bound | New candidate | Accepted |
| --- | ---: | ---: | --- |
| (0,0) | 5.329123828160... | 5.340241786049... | Current bound |
| (0,1) | 1.490954924245... | 1.479385167145... | New candidate |
| (0,2) | 0.175122098324... | 0.175119677184... | New candidate |
| (1,0) | 1.689617393530... | 1.676111556333... | New candidate |
| (2,0) | 0.234158647741... | 0.234129789764... | New candidate |

The exact coefficients and rational candidates are retained in the
certificate. Each cost keeps the minimum of its own current and new
upper bounds. Comparing against an earlier public row would wrongly
count an additional gain for tuple00 and overstate other gains.

All five original quadratic weights are2371/2880. The accepted four
rows reduce the complete numerator by exactly

    1142571154044081850503886997
      /55277902592312400000000000000
    =0.02066958224646861567033911172359....         (FT15)

One simultaneous legal substitution in the existing52 all-load
majorants supplies zero further improvement. The complete signed
numerator remains

    N=r_mass*(53/360)+sum_(i=1..52)weight_i*cost_i
                                      +c_square*(374/75),
    r_mass<0, weight_i>0, c_square>0.

It equals

    138994272332498675172774630998611476091466279743
      /3952702451597549034231858077472656250000000000.

The full101 AP11 denominator and its infinite affine tail are
unchanged. With C0=185694867601/8599322160, the final comparison is

    716222699946927632837956597381642058997115043314859
      /1544116031429162385179130957682216048828125000000,

which is(FT1). No face result is substituted into an off-face or
global comparison.

## Reproduction

[whole_face_second_factorial_tail.py](../frontier/whole_face_second_factorial_tail.py)
checks the complete cap rows and pair partition, all12500 original
head layouts, exact quadratic expansions, the five current104 row
comparisons, all52 signed numerator costs and101's complete positive
denominator. The
[certificate](../certificates/source_norms/whole_face_second_factorial_tail.json)
uses schema `erdos7-whole-face-second-factorial-tail-v1` and retains
all exact terms, maximizing layouts, tail reconstructions and accepted
cost bounds.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/whole_face_second_factorial_tail.py --output docs/reports/erdos7-odd-covering/certificates/source_norms/whole_face_second_factorial_tail.json
python3 -I -O docs/reports/erdos7-odd-covering/frontier/whole_face_second_factorial_tail.py --check
```
