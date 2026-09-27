[Index](../../marked_head_profile.md) · [Extremal original family](../321-384/350-extremal-paired-branch-and-source-support.md) · [Composite budget](../321-384/361-prime-overlap-reservation-for-composite-parents.md) · [Saturated fibres](378-saturated-prime-fibres-and-mixed-tail-incidence.md) · [Literal root costs](379-root-forest-disintegration-and-residue-costs.md)

# Small-prime survivors give lower bounds on the original Haar budget

In the saturated three-root branch of report 378, the missing nonzero
5-root is a literal full fibre covered by original 3-free classes.
Restricting to this fibre gives a covering with residual multiplicity
at most two. Its low-prime reciprocal capacity forces positive original
Haar mass from moduli containing primes at least 11 and at least 13.
Removing the actual pure-power classes turns these into lower bounds
on report 361's composite budget.

Independently of the first-5 branch, the existing 3,5,7 survivor estimate
gives

\[
 M_{\mathrm{comp}}\ge
 \frac{(53/135)X-F}{P_*}>
 \frac{44X}{135P_*},
\]

where \(X\) is the original pure-power survivor density,
\(F\) is the finite reciprocal capacity of full-support divisors,
and \(P_*\) is the largest actual support prime.
A divisor-support capacity bound also removes the largest-prime factor:
\(M_{\mathrm{comp}}>X/140\) at every finite height and for arbitrary
additional support primes. Section 8 shows that this uniform floor is
already implied by report 361's exact no-prime-region coverage condition
and the same divisor-capacity bound. It therefore adds no exclusion of an
original modulus palette that passes that existing condition. The joint
budget form retains the excess inside the no-prime region.
These are ordinary mathematical deductions from the cited reports and
the finite Euler product.
They do not establish unrestricted noncoverage, new Lean content,
or literature novelty.

## 1. The original family, its pure survivors, and its composite budget

Assume a distinct odd whole covering exists and choose the
lexicographically extremal original family of
[350, EB1--EB3](../321-384/350-extremal-paired-branch-and-source-support.md):

\[
 \mathcal C=\{A_d=a_d\bmod d:d\in D\},\qquad
 Q=\mathop{\mathrm{lcm}}D=\prod_{p\in\Lambda}p^{H_p}.
 \tag{HB1}
\]

The original moduli are distinct and greater than one. The set \(D\)
is divisor-closed above one; comparable original classes are disjoint;
and a common CRT translation gives \(A_p=0\bmod p\) for every support
prime. The support \(\Lambda\) is an initial segment of the odd primes.
It contains 3,5,7: the positive 3,5,7 survivor estimate recalled in
section 5 excludes a whole cover supported on a subset of these primes.
All heights \(H_p\) are the original finite heights.

Write \(\mathsf H\) for uniform probability on \(\mathbb Z/Q\mathbb Z\).
Every original prime power \(p^a\), \(1\le a\le H_p\), belongs to \(D\).
Their classes are pairwise disjoint in the \(p\)-coordinate. Thus the
actual pure-power survivor set \(S_p\) has density

\[
 y_p=\sum_{a=1}^{H_p}p^{-a},\qquad
 x_p=1-y_p>0,\qquad
 X=\prod_{p\in\Lambda}x_p.
 \tag{HB2}
\]

Every product over high primes below ranges only over primes in
\(\Lambda\), with their original heights. An empty product is one.
Here a **mixed** modulus has at least two distinct prime factors.
A **composite** modulus is any nonprime modulus, including a pure power
\(p^a\) with \(a\ge2\). Denote these original subsets by
\(D_{\mathrm{mix}}\) and \(D_{\mathrm{comp}}\), respectively.

Retain exactly the budget from
[361, PR5](../321-384/361-prime-overlap-reservation-for-composite-parents.md):

\[
 \begin{aligned}
 M_{\mathrm{comp}}
 &=\sum_{d\in D_{\mathrm{comp}}}\frac{c_d}{d},\\
 c_d&=1-\prod_{\substack{p\in\Lambda\\p\nmid d}}
                  \left(1-\frac1p\right).
 \end{aligned}
 \tag{HB3}
\]

This is an original-Haar quantity. Equivalently, it is
\(\int t\,\mathbf1_{\{k\ge1\}}\,d\mathsf H\), where \(k\) and \(t\)
count the original prime and composite classes covering the same point.

## 2. A missing nonzero 5-root gives an actual two-copy quotient

Put \(B=Q/3^{H_3}\) and let

\[
 R_3=(\mathbb Z/B\mathbb Z)\setminus
          \bigcup_{\substack{d\in D\\3\nmid d}} A_d^B,
 \tag{HB4}
\]

where \(A_d^B\) is the original 3-free class on the full 3-free carrier.
[Report 378](378-saturated-prime-fibres-and-mixed-tail-incidence.md)
gives \(|\operatorname{pr}_5R_3|\in\{3,4\}\).
Assume in this section that it equals three. Since the original
\(A_5=0\bmod5\) excludes zero, exactly one nonzero root \(v\bmod5\)
is absent. Therefore the entire fibre

\[
 F_v=\{x\bmod B:x\equiv v\bmod5\}
 \tag{HB5}
\]

is covered by original 3-free classes.

Use the literal branch restriction of
[350, EB4--EB6](../321-384/350-extremal-paired-branch-and-source-support.md),
here parametrized by
\(\theta(z)=v+5z\) from \(\mathbb Z/(B/5)\mathbb Z\) onto \(F_v\).
For an original 3-free modulus \(d=5^ar\), \(5\nmid r\), its nonempty
pullback has modulus

\[
 d^\downarrow=
 \begin{cases}
 r,&a=0,\\
 5^{a-1}r,&a\ge1\text{ and }a_d\equiv v\pmod5.
 \end{cases}
 \tag{HB6}
\]

All other pullbacks are empty. These pullbacks cover the whole quotient
carrier. At positive output 5-exponent, the input exponent is uniquely
one larger, so the numerical output modulus occurs at most once.
At output 5-exponent zero it occurs at most twice, from originals
\(r\) and \(5r\). Modulus one is absent: no original modulus is one,
and \(A_5\) misses \(F_v\).

There must be a repeated output modulus. Otherwise these pullbacks
would be a distinct odd nonunit whole cover with fewer classes than
\(\mathcal C\), contradicting minimum cardinality in 350, EB1.
Consequently there is an actual pair

\[
 r,5r\in D,\qquad r>1,\qquad (r,15)=1,\qquad
 A_{5r}^B\cap F_v\ne\varnothing.
 \tag{HB7}
\]

The original \(r\)-class also meets \(F_v\). Their quotient residues
modulo \(r\) are different, since equality would make the comparable
original classes intersect. This uses the existing minimality argument;
no external distinct-cover theorem is needed. Arbitrary original
prime-power heights and all active original labels are retained.

## 3. Finite low-prime capacity forces high-prime Haar mass

Let \(K=H_5\), choose
\(L\subseteq\Lambda\setminus\{3,5\}\), and put

\[
 E_L=\prod_{\ell\in L}\sum_{j=0}^{H_\ell}\ell^{-j},
 \qquad z_5=\sum_{j=1}^{K-1}5^{-j}.
 \tag{HB8}
\]

The second sum is empty at \(K=1\).
Among quotient classes supported on \(\{5\}\cup L\), the zero
5-exponent contributes at most \(2(E_L-1)\); positive 5-exponents
contribute at most \(z_5E_L\). Thus their union has normalized quotient
Haar mass at most

\[
 R_L=(2+z_5)E_L-2,\qquad
 \eta_L=1-R_L=3-(2+z_5)E_L.
 \tag{HB9}
\]

Suppose \(\eta_L>0\). The uncovered quotient portion must be covered by
original 3-free classes meeting \(F_v\) whose moduli contain a prime
outside \(\{5\}\cup L\). Call this actual label set \(\mathcal K_L\).
The quotient density of each such class is exactly
\(5^{\mathbf1_{\{5\mid d\}}}/d\). The union bound gives

\[
 \sum_{d\in\mathcal K_L}\frac{5^{\mathbf1_{\{5\mid d\}}}}d
 \ge\eta_L,\qquad
 \sum_{d\in\mathcal K_L}\frac1d\ge\frac{\eta_L}{5}.
 \tag{HB10}
\]

Finite heights give \(z_5<1/4\). Taking \(L=\{7\}\) gives
\(E_L<7/6\), hence \(R_L<5/8\) and \(\eta_L>3/8\).
In particular,

\[
 \sum_{\substack{d\in D,\ 3\nmid d\\
       \exists r\in\Lambda,\ r\ge11:\ r\mid d\\
       A_d^B\cap F_v\ne\varnothing}}\frac1d>\frac3{40}.
 \tag{HB11}
\]

This forces a support prime at least 11, so the initial-segment support
contains 11. Now take \(L=\{7,11\}\). Then \(E_L<77/60\),
\(R_L<71/80\), and \(\eta_L>9/80\), giving

\[
 \sum_{\substack{d\in D,\ 3\nmid d\\
       \exists r\in\Lambda,\ r\ge13:\ r\mid d\\
       A_d^B\cap F_v\ne\varnothing}}\frac1d>\frac9{400}.
 \tag{HB12}
\]

The constants hold at every finite height. The summands are ordinary
original reciprocal masses; HB11--HB12 may still include pure high-prime
powers.

## 4. Deleting pure powers gives a charge on the same composite budget

For \(P=7\) or \(11\), take respectively \(L=\{7\}\) or \(\{7,11\}\).
Let \(E\subseteq F_v\) be the part avoiding every original 3-free class
supported on \(\{5\}\cup L\). Its normalized fibre mass is at least
\(\eta_L\). This event depends only on the low coordinates.

Restrict every actual coordinate \(r>P\) to its pure-power survivor
\(S_r\). Under original Haar these coordinates are independent of the
low-coordinate event \(E\), so, writing \(\mathsf H_B\) for uniform
probability on the complete carrier \(B\),

\[
 \mathsf H_B\left(E\cap\bigcap_{\substack{r\in\Lambda\\r>P}}S_r\right)
 =\mathsf H_B(E)\prod_{\substack{r\in\Lambda\\r>P}}x_r
 \ge\frac{\eta_L}{5}
             \prod_{\substack{r\in\Lambda\\r>P}}x_r.
 \tag{HB13}
\]

Here each \(S_r\) denotes its full inverse image in \(B\).
Lifting to the original period adds a free 3-coordinate and preserves
this mass. No independence is asserted after conditioning on mixed
classes.

Every point of this set is covered by a 3-free original, because it
lies in \(F_v\). All low-supported originals have been deleted, as have
all pure high-prime powers. Hence some original **mixed** class with
a prime \(r>P\) must cover it. Applying the original-Haar union bound,
and then enlarging the sum to all such originals, gives

\[
 \begin{aligned}
 \sum_{\substack{d\in D_{\mathrm{mix}},\ 3\nmid d\\
           \exists r\in\Lambda,\ r\ge11:\ r\mid d}}\frac1d
 &>\frac3{40}\prod_{\substack{r\in\Lambda\\r\ge11}}x_r,\\
 \sum_{\substack{d\in D_{\mathrm{mix}},\ 3\nmid d\\
           \exists r\in\Lambda,\ r\ge13:\ r\mid d}}\frac1d
 &>\frac9{400}\prod_{\substack{r\in\Lambda\\r\ge13}}x_r.
 \end{aligned}
 \tag{HB14}
\]

Every counted modulus omits 3, so its coefficient \(c_d\) in HB3 is
at least \(1/3\). The saturated branch therefore satisfies

\[
 \begin{aligned}
 M_{\mathrm{comp}}&>
       \frac1{40}\prod_{\substack{r\in\Lambda\\r\ge11}}x_r,\\
 M_{\mathrm{comp}}&>
       \frac3{400}\prod_{\substack{r\in\Lambda\\r\ge13}}x_r.
 \end{aligned}
 \tag{HB15}
\]

These are lower bounds on the existing budget, obtained from literal
subsets of the original carrier. The conditional laws constructed in
378 and 379 are not used as Haar measures.

## 5. The 3,5,7 survivor estimate gives a bound in both branches

The existing
[CM1--CM2 estimate](../../problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md)
states that, under the product of uniform laws on the actual pure
3-,5-,7-power survivors, the union of all actual mixed classes
supported on \(\{3,5,7\}\) has probability at most \(82/135\).
Its complement therefore has conditional probability at least
\(53/135\), for arbitrary finite heights and actual assigned residues.

Let \(G_{357}\) be that complement inside \(S_3\times S_5\times S_7\).
Then its ambient low-coordinate Haar mass is at least
\((53/135)x_3x_5x_7\). Form the actual subset of the original carrier

\[
 G=G_{357}\times
      \prod_{\substack{p\in\Lambda\\p\ge11}}S_p.
 \tag{HB16}
\]

Only this explicit CRT product is used. It has
\(\mathsf H(G)\ge(53/135)X\), avoids every pure-power original, and
avoids every original supported on \(\{3,5,7\}\). Whole coverage forces

\[
 \sum_{\substack{d\in D_{\mathrm{mix}}\\
           \exists p\in\Lambda,\ p\ge11:\ p\mid d}}\frac1d
 \ge\frac{53}{135}X.
 \tag{HB17}
\]

This argument applies in both the three-root and four-root first-5
branches. It does not convert 379's residue-dependent prices into
reciprocal weights; it supplies a separate lower bound directly from
the actual original-Haar survivor.

## 6. Remove full-support capacity and retain the original budget

Put

\[
 P_*=\max\Lambda,\qquad F=\prod_{p\in\Lambda}y_p.
 \tag{HB18}
\]

The finite divisor Euler product gives

\[
 \sum_{\substack{d\in D\\\operatorname{supp}(d)=\Lambda}}\frac1d
 \le
 \sum_{\substack{d\mid Q\\\operatorname{supp}(d)=\Lambda}}\frac1d
 =F.
 \tag{HB19}
\]

A full-support modulus has \(c_d=0\). Every proper-support modulus
omits some \(p\in\Lambda\), so
\(c_d\ge1/p\ge1/P_*\). Removing the full-support contribution from
HB17 and using HB3 therefore yields

\[
 M_{\mathrm{comp}}\ge
       \frac{(53/135)X-F}{P_*}.
 \tag{HB20}
\]

The right side is positive. At every finite original height,

\[
 \frac{y_p}{x_p}
 =\frac{1-p^{-H_p}}{p-2+p^{-H_p}}
 <\frac1{p-2}.
 \tag{HB21}
\]

Since \(\Lambda\) contains 3,5,7,
\(F/X<\prod_{p\in\Lambda}(p-2)^{-1}\le1/15\).
Consequently

\[
 M_{\mathrm{comp}}\ge
       \frac{(53/135)X-F}{P_*}
       >\frac{44X}{135P_*}.
 \tag{HB22}
\]

All factors refer to one original palette and its finite heights.
When the saturated-branch hypotheses hold, HB22 and HB15 are simultaneous
lower bounds on the same \(M_{\mathrm{comp}}\). Their maximum is also a
lower bound; no disjoint allocation has been established that would
permit adding them.

## 7. A divisor-support capacity bound removes the largest-prime factor

The full-support estimate charges every other modulus at the smallest
possible coefficient, which decreases as the largest prime grows.
The reciprocal capacity of all moduli with a small coefficient gives
a bound without that factor.

Extend the numerical coefficient in HB3 to every positive divisor of
\(Q\), including one. For \(0<t<1\), define the finite capacity

\[
 C(t)=\sum_{\substack{d\mid Q\\c_d\le t}}\frac1d.
 \tag{HB23}
\]

Let \(\mathcal K\) be the actual mixed originals containing a prime at
least 11, as in HB17. Distinctness of the original moduli gives
\(\sum_{d\in\mathcal K,\,c_d\le t}1/d\le C(t)\). Keeping only the
remaining actual originals in the nonnegative sum HB3 yields

\[
 M_{\mathrm{comp}}\ge
 t\left(\frac{53}{135}X-C(t)\right).
 \tag{HB24}
\]

Including divisor one or divisors absent from the original family in
HB23 only enlarges this upper capacity. No new congruence classes or
replacement of the original Haar law is asserted.

For any positive integer \(k\), the pointwise inequality

\[
 \mathbf1_{\{c_d\le t\}}
 \le (1-t)^{-k}(1-c_d)^k
\]

and the finite exponent-coordinate expansion, using the same coordinates
as the existing
[divisor Euler-product interface](../../../../../D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct.lean),
give

\[
 \begin{aligned}
 C(t)&\le (1-t)^{-k}
       \sum_{d\mid Q}\frac1d
          \prod_{\substack{p\in\Lambda\\p\nmid d}}(1-1/p)^k\\
     &=(1-t)^{-k}
       \prod_{p\in\Lambda}\bigl[y_p+(1-1/p)^k\bigr].
 \end{aligned}
 \tag{HB25}
\]

The product identity is a sum over the divisor exponent coordinates:
a zero exponent contributes \((1-1/p)^k\), and the positive exponents
contribute \(y_p\). It is a capacity calculation on labels, not an
independence assertion about conditioned surviving residues.

For fixed \(b\ge0\), the ratio \((y+b)/(1-y)\) increases with
\(0\le y<1\). Since \(y_p<1/(p-1)\), division by the same \(X\) gives

\[
 \frac{C(t)}X\le(1-t)^{-k}\prod_{p\in\Lambda}R_p(k),\qquad
 R_p(k)=\frac{1+(p-1)(1-1/p)^k}{p-2}.
 \tag{HB26}
\]

Every further prime can be discarded from this upper bound when
\(k\ge4\). Indeed, for \(p\ge5\),

\[
 p^4(p-3)-(p-1)^5
 =2p^3(p-5)+5p(2p-1)+1>0.
\]

It follows that \((1-1/p)^4<(p-3)/(p-1)\), hence
\(R_p(k)\le R_p(4)<1\). The support contains 3,5,7, so HB26 implies

\[
 \frac{C(t)}X\le(1-t)^{-k}R_3(k)R_5(k)R_7(k)
 \qquad(k\ge4).
 \tag{HB27}
\]

This step is uniform in every additional prime and in all original
heights. Take \(k=20\) and \(t=1/25\). Exact integer comparisons give

\[
 R_3(20)<\frac{1001}{1000},\qquad
 R_5(20)<\frac7{20},\qquad
 R_7(20)<\frac{13}{50},\qquad
 \left(\frac{25}{24}\right)^{20}<\frac{23}{10}.
 \tag{HB28}
\]

Consequently

\[
 \frac{C(1/25)}X<\frac{2095093}{10000000},
 \qquad
 M_{\mathrm{comp}}>
 \frac{49432489}{6750000000}X>\frac{X}{140}.
 \tag{HB29}
\]

The final rational margin over \(X/140\) is
\(8527423X/47250000000>0\). No optimality of the chosen parameters is
claimed. HB29 retains the actual finite product \(X\); it is not a
positive absolute lower bound as the support grows. HB22 and HB29 hold
in both branches; when the saturated-branch hypotheses of HB15 also hold,
all three bounds may be combined by taking their maximum, without adding
their overlapping charges. This is a direct use of divisor-factorized
capacity after an original-Haar reduction; it does not order 379's
forest-law prices by the golden resource objective.

## 8. The exact no-prime budget already implies the uniform floor

Keep the same finite original support, heights and distinct modulus set.
With \(\varphi\) denoting Euler's totient, put

\[
 \begin{aligned}
 P_0&=\prod_{p\in\Lambda}(1-1/p),&
 W&=\sum_{d\in D_{\mathrm{comp}}}\frac1d,\\
 A&=P_0\sum_{d\in D_{\mathrm{comp}}}\frac1{\varphi(d)},&
 v&=A-P_0.
 \end{aligned}
 \tag{HB30}
\]

The exact identity in
[361, PR6](../321-384/361-prime-overlap-reservation-for-composite-parents.md)
is \(M_{\mathrm{comp}}=W-A\). Here \(A\) is the total composite load
in the region avoiding every original prime class, whose Haar mass is
\(P_0\). Whole coverage therefore requires \(A\ge P_0\), equivalently
\(\sum_{d\in D_{\mathrm{comp}}}1/\varphi(d)\ge1\), and \(v\ge0\).
This condition is already part of PR6. Also \(X\le P_0\), since
\(y_p\ge1/p\) at every original height.

Writing \(h=\sum_{d\in D}1/d-1\) and
\(J=\sum_{p\in\Lambda}1/p-1+P_0\), the presence of every support
prime in \(D\) gives

\[
 h-J=W-P_0=M_{\mathrm{comp}}+v.
 \tag{HB31}
\]

Apply the threshold split from section 7 to all original composite
labels. At most \(C(t)\) of their reciprocal mass has \(c_d\le t\).
For every \(0<t<1\), this yields

\[
 \begin{aligned}
 M_{\mathrm{comp}}&\ge t\bigl(W-C(t)\bigr),\\
 (1-t)M_{\mathrm{comp}}&\ge t\bigl(A-C(t)\bigr).
 \end{aligned}
 \tag{HB32}
\]

This finite label inequality does not require whole coverage or the
mixed-head survivor estimate. It also permits an empty composite subset;
whole coverage supplies the separate requirement \(A\ge P_0>0\).

Use the already established strict capacity bound in HB29 and set
\(\alpha=2095093/10000000\). At \(t=1/25\), HB32 gives the joint form

\[
 \begin{aligned}
 24M_{\mathrm{comp}}+\alpha X&>A=P_0+v,\\
 24(h-J)+\alpha X&>P_0+25v,\\
 W&>\frac{25(P_0+v)-\alpha X}{24}.
 \end{aligned}
 \tag{HB33}
\]

The strictness comes from \(C(1/25)<\alpha X\); no new approximation
of the original heights or law is used. Under the existing coverage
condition \(A\ge P_0\ge X\), it follows that

\[
 M_{\mathrm{comp}}>\frac{1-\alpha}{24}X>\frac{X}{140}.
 \tag{HB34}
\]

For the last comparison, \(\alpha<1/4\) gives
\((1-\alpha)/24>1/32>1/140\).
Consequently HB29's uniform floor cannot exclude any exact original
palette that already satisfies the no-prime-region union condition.
HB32 and HB33 express a universal relation between divisor-label
capacities, even without coverage, with \(v=A-P_0\) defined algebraically.
They are useful budget summaries, not an independent new palette test.

The same limitation applies to a period-only comparison with the
[odd 315 resource envelope](../../problem-details/02-current-bounds-and-comparisons.md#reuse-of-the-5040-and-divisor-sum-work).
If the full nonunit divisor palette of \(Q\) passes the no-prime
condition, that numerical palette also satisfies HB32--HB34 and the
divisor-sum envelope. Those scalar constraints alone cannot exclude
such a period. This is an obstruction to that comparison, not a claim
that the full palette has a covering residue assignment or satisfies
all extremal and private-point constraints.

## 9. The remaining comparison

[361, PR4--PR6](../321-384/361-prime-overlap-reservation-for-composite-parents.md)
already supplies \(M_{\mathrm{comp}}\le h-J\) on the same original
Haar space. By HB31 this upper bound is exactly \(v\ge0\), so it cannot
contradict the uniform floor it already implies together with the
divisor-capacity inequality. No incompatibility with the saturated-branch
bounds has been proved either. A stronger exclusion requires an additional
restriction on this same original budget or its jointly realizable
sources, retaining the original labels, heights and coverage constraints.

The missing-fibre quotient is a whole-cover reduction with at most two
copies of each output modulus. Its heights are unrestricted and several
composite output moduli may repeat. The reduction and the positive Haar
charges above do not themselves rule it out or settle Erdős #7.
