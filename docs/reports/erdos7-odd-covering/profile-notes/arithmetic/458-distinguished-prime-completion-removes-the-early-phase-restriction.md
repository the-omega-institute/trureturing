# Changing the distinguished prime gives an arbitrary-phase weighted completion law

For the full core supported on \(\{3,5,7,11\}\), choose any distinguished odd prime \(r\ge13\). At arbitrary finite core and \(r\)-heights, and with arbitrary original residue choices, there is an actual core set of Haar mass greater than \(29/8080\) on which the original \(r\)-weighted completion load is at most \(1313/120\). Its margin below the whole-cover threshold is at least \(39/40\). This set supports one probability law that extends across arbitrary finite outside-prime supports and heights above a core-height-independent cutoff.

The conclusion concerns the original weighted completion interface. It removes the early-phase restrictions of reports456–457 by choosing a different distinguished prime; it does not establish their original \(3\)-weighted statement at arbitrary phases. Choosing \(r\) changes both the completion functional and the subfamily called old. It is not an arithmetic symmetry transporting a \(3\)-certificate. The deduction uses existing head bounds and the tail construction of [report455](455-positive-mass-core-margins-give-height-independent-tail-cutoffs.md). [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) already gives a stronger bare noncoverage range. No new Lean certification or unrestricted Erdős #7 conclusion is claimed.

## Original family and its distinguished-prime threshold

Let \(K\) have prime support contained in \(\{3,5,7,11\}\), with all its finite heights resolving the complete original family. Unused core coordinates may be padded with height one. Let \(r\ge13\) be prime, let \(H\ge1\) resolve every original \(r\)-exponent, and allow at most one original residue \(\alpha_d\) for each numerical modulus \(d>1\). The core moduli divide \(r^H K\). Missing moduli are allowed.

Write \(\lambda\) for Haar probability on \(\mathbb Z/K\mathbb Z\), and let \(S\) avoid every actual \(r\)-free core class. For \(x\in S\), define

\[
 \ell_{r,H}(x)=\sum_{\substack{d=r^e a\ \mathrm{original}\\1\le e\le H,\ a\mid K,\ a>1}}
     r^{1-e}\mathbf1_{x\equiv\alpha_d\pmod a}.
 \tag{DP1}
\]

Each summand retains its original numerical label and actual cofactor phase. Different \(r\)-depths are not identified even when their cofactor events coincide. Pure powers of \(r\), corresponding to \(a=1\), are excluded from (DP1). Their entire possible cost is reserved in

\[
 T_{r,H}=\sum_{e=1}^H r^{1-e}
        ={r\over r-1}(1-r^{-H}),\qquad
 B_{r,H}=r-T_{r,H}
        ={r(r-2)\over r-1}+{r^{1-H}\over r-1}.
 \tag{DP2}
\]

At a fixed \(r\)-free word, each active original \(r^e\)-prefix has Haar mass \(r^{-e}\). If the complete original family covers, its active mixed prefixes and pure prefixes must cover the whole \(r\)-coordinate. The union bound therefore forces total weighted mixed completion at least \(B_{r,H}\), pointwise on the complete actual \(r\)-free residual, and hence under every probability supported there. Missing pure labels only strengthen that necessity. No parent-phase compatibility is assumed in this upper bound on union size.

For every \(r\ge13\),

\[
 T_{r,H}\le{13\over12},\qquad B_{r,H}\ge{143\over12}.
 \tag{DP3}
\]

## An arbitrary-phase core set with a uniform margin

Use the uniform law \(\mu=\lambda(\cdot\mid S)\) on the complete actual old survivor set. [Chapter10](../../problem-details/10-a-four-prime-head-and-a-restricted-noncoverage-theorem.md), (P3)–(P5), proves its existence at every finite height and gives the full-support cylinder coefficient \(720/29\). Applying this bound to a full atom yields

\[
 \lambda(S)\ge{29\over720}.
 \tag{DP4}
\]

Equivalently, the existing profile certificate records relative pure-product survivor fraction \(58/405\); multiplying by the pure-domain lower bound \((1/2)(3/4)(5/6)(9/10)=9/32\) gives the same value. Padding unused coordinates does not add forbidden classes or alter survivor density.

The same actual uniform survivor law satisfies Chapter10 (P2):

\[
 \Gamma_K(\mu)\le C_4={4939031\over47730}.
 \tag{DP5}
\]

Let

\[
 R_\mu=\sum_{1<a\mid K}\max_b\mu(b\bmod a).
\]

Choose one maximizing residue for each divisor, all within the same layout and law, and include the unit divisor. Jensen's inequality for its complete load gives

\[
 (1+R_\mu)^2\le\Gamma_K(\mu)
   \le C_4 < \left({51\over5}\right)^2.
 \tag{DP6}
\]

The exact final slack is \(133991/238650\). Thus \(R_\mu<46/5\). Each original positive-\(r\)-depth layout is a partial selection of these nonunit divisors, so (DP1)–(DP3) imply, under this one \(\mu\),

\[
 \mathbb E_\mu\ell_{r,H}
 \le T_{r,H}R_\mu
 <{299\over30}
 ={143\over12}-{39\over20}.
 \tag{DP7}
\]

Define the actual good set

\[
 A=\{x\in S:\ell_{r,H}(x)\le1313/120\}.
\]

Nonnegativity and Markov's inequality give

\[
 \mu(A)>1-\frac{299/30}{1313/120}={9\over101},\qquad
 \lambda(A)>{29\over720}{9\over101}={29\over8080}.
 \tag{DP8}
\]

Every point of \(A\) satisfies

\[
 \ell_{r,H}\le{1313\over120}
 ={143\over12}-{39\over40}
 \le B_{r,H}-{39\over40}.
 \tag{DP9}
\]

Consequently the one law \(\mu_A=\lambda(\cdot\mid A)\) has full-core Haar density less than \(8080/29<279\). The set depends on the actual complete core phases; it is not selected in advance of those phases. All estimates are uniform in their finite heights and in \(r\ge13\).

## The tail bridge keeps the same constants for every odd distinguished prime

The proof of report455 applies with any distinguished odd prime \(r\ge3\), provided \(\gcd(r,K)=1\). The core may contain 3. For clarity, retain the auxiliary cutoff

\[
 E_q=\min(H,\lfloor\log_3 q\rfloor)
 \tag{DP10}
\]

at each largest outside prime \(q\). This is a cutoff on the exponent label \(e\) of the actual modulus \(r^e a b\); it does not replace \(r\) by 3 in any numerical modulus or residue.

For a divisor inventory \(Q\mid K\), allow all original tail moduli

\[
 d=r^e a\prod_{q\in T}q^{f_q},\qquad
 a\mid Q,\quad0\le e\le H,\quad
 \varnothing\ne T\subseteq P,\quad1\le f_q\le J_q,
 \tag{DP11}
\]

where \(P\) is a finite set of outside primes disjoint from the prime support of \(rK\). Original phases, finite outside heights, support sizes and co-occurrence graphs are unrestricted.

Start with any core probability of full Haar density at most \(\Lambda\), supported on a declared good set avoiding all actual \(r\)-free core classes. The early original pair count in report455 uses only \(E_q+1\), numerical distinctness, the actual cofactor intersections and the same core probability. It is unchanged by the choice of \(r\). The capped kernels therefore give the same global failure bound

\[
 \epsilon\le{108\Lambda J_2(Q)(1+\ln B)^2\over B}<3^{-240},
 \qquad
 J_2(Q)=\sum_{a,b\mid Q}{1\over\operatorname{lcm}(a,b)},
 \tag{DP12}
\]

whenever every outside prime is at least

\[
 B\ge3^{256}N^3,\qquad N=\lceil\Lambda J_2(Q)\rceil.
 \tag{DP13}
\]

Condition the global joint capped law once on avoiding every early cofactor event. This includes all \(e=0\) tail events and produces one probability \(\nu\) on the complete actual \(r\)-free residual. Its core marginal remains supported on the good set and satisfies the same domination and total-variation bounds as report455. Its entire core marginal need not equal the input marginal.

For every positive depth, \(r^{1-e}\le3^{1-e}\). Thus the late weights under (DP10) obey exactly the same bound as in report455:

\[
 \sum_{e>E_q}r^{1-e}\le\sum_{e>E_q}3^{1-e}\le{9\over2q},
\]

when any late depth exists. The subsequent original-label sum on this same \(\nu\) yields

\[
 L_{\rm tail}^{(r)}(\nu)
 \le{324\Lambda J_1(Q)\over B}<3^{-250},\qquad
 J_1(Q)=\sum_{a\mid Q}{1\over a}.
 \tag{DP14}
\]

No factor depending on \(r\), the number of parent depths, or the number of outside primes is introduced. This is an application of the existing proof with a conservative auxiliary cutoff, not a new independent kernel theorem.

## The concrete all-phase completion interface

Apply (DP10)–(DP14) to \(\mu_A\), with \(\Lambda=279\). For the complete core prime inventory,

\[
 J_1(Q)\le{77\over32},\qquad
 J_2(Q)\le{231\over20},\qquad
 N\le\left\lceil279\,{231\over20}\right\rceil=3223.
 \tag{DP15}
\]

Therefore the single cutoff

\[
 B\ge3^{256}\,3223^3
 \tag{DP16}
\]

works for every admitted finite core height, parent height and outside configuration. The resulting actual supported probability satisfies

\[
 L_{\rm core}^{(r)}(\nu)\le{1313\over120},\qquad
 L_{\rm tail}^{(r)}(\nu)
 \le{324\cdot279\cdot77\over32B}<3^{-250}<{39\over40}.
 \tag{DP17}
\]

Its total original weighted completion is strictly below \(B_{r,H}\). Every label uses this one final law; the pointwise core bound survives its marginal change. This contradicts the whole-cover necessity in (DP2) for any hypothetical cover in the stated class.

## Controls and remaining scope

The [arithmetic and literal-family control](../../frontier/cover-geometry/distinguished_prime_completion.py) and [exact data](../../frontier/cover-geometry/distinguished_prime_completion.json) consume the existing head-bound certificates and check every displayed rational parameter. Two literal families use distinguished primes 13 and 17, core period 3, parent height 3, and outside primes 5 and 7. Each retains all 30 distinct original odd numerical moduli and their actual CRT residues. These small outside primes use measured survival, not the asymptotic cutoff (DP16).

Both controls exercise five positive-history low-density kernel branches and five high-density branches. One global conditioning has survival 53/105 and changes the core marginal from (1/2,1/2) to (18/53,35/53). Under that same final law, all early cofactor events vanish and 192 joint-cylinder queries per family satisfy their bounds. The actual weighted tails are 36/8957 and 36/15317, each at most the base-three majorant 4/53. Literal enumeration of 21,970 and 49,130 full CRT points, respectively, verifies every positive-law parent fibre against the original union-capacity bound; the average actual parent-fibre escapes are 103470/116441 and 238618/260389.

These controls verify the finite implementation and its interpretation, including a changed core marginal. The universal phase and height claims use the ordinary arguments above and their stated source theorems. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/distinguished_prime_completion.py
```

Output defaults to JSON on stdout; `--output PATH` selects a file. Checks remain active in optimized mode.

The source bounds and ordinary deductions do not provide a good-core theorem for an arbitrary finite prime inventory. Absorbing further primes into the core can change its survivor law, cylinder costs and available margin. Nor do (DP8)–(DP17) answer whether arbitrary phases on the original \(\{5,7,11,13\}\) core admit a \(3\)-weighted margin. The parent change supplies a different, fully specified weighted interface. Chapter33 already excludes the displayed bare prime-support range at much smaller cutoffs, so the contribution here is that interface and its one-law tail extension.
