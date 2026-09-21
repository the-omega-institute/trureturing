[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

<a id="fixed-order-scalar-threshold-barrier-and-cofactor-colors"></a>
# Fixed-order scalar thresholds cannot close the additive ledger

For the fixed prime order \((5,7,11,13,17,19)\), the independent-run
additive-hinge model defined below has the exact global minimum
\[
 \frac{38015512875791085444068380947478658842921999427}
      {37918700535989642067334158824877050925450000000}
 =1.002553155525716295\ldots>1
 \tag{ST1}
\]
over all real deterministic thresholds in its domain. It is attained
at \((0,1,3,5,7,9)\). Thus retuning these thresholds cannot give a
positive reserve from this scalar ledger. The result concerns this
comparison model, not an actual covering counterexample or a lower bound
on actual deleted mass. A different prime order, history-dependent
thresholds, different starting laws, retained anchor geometry and
first-hit accounting are outside the statement.

The proof reduces every real threshold vector to an integer vector with
no larger cost, then evaluates all 378,675 integer vectors by exact
rational arithmetic, retaining the complete infinite-height mean.
The supplied producer is self-contained and uses no optimizer or
floating-point comparison. This is an ordinary proof with an exact
certificate; no Lean verification is claimed.

## 1. The fixed model and its entire real domain

Put \(p=(5,7,11,13,17,19)\), \(d_i=p_i-2\). Let the root run have
\[
 \Pr(K_0\ge a)=2\,3^{-a}\qquad(a\ge1).
\]
For deterministic \(0\le t_i<d_i\), let the child runs be independent
of the root and one another, with
\[
 C_i=\frac{p_i-1}{d_i-t_i},\qquad
 \Pr(K_i\ge a)=\min\{1,C_ip_i^{-a}\}\quad(a\ge1).
 \tag{ST2}
\]
The minimum with one includes saturated schedules. Define
\[
 Y_i=(1+K_0)\prod_{1\le j<i}(1+K_j),\qquad R_i=Y_i-1,
 \qquad
 S(t)=\sum_{i=1}^6\frac{\mathbb E(R_i-t_i)_+}{d_i-t_i}.
 \tag{ST3}
\]
Every expectation is finite: \(\mathbb EK_i\le C_i/(p_i-1)<\infty\)
and each product has finitely many independent factors. The sixth run
does not enter a later charge; its threshold still enters the sixth
summand. No limit of a finite-height objective replaces (ST3).

### The terminal interval cannot improve a threshold

Fix all thresholds except \(t_i\). Its earlier load \(R_i\) is
integer-valued and independent of this threshold. For
\(d_i-1\le t_i<d_i\),
\[
 \frac{d}{dt_i}\frac{\mathbb E(R_i-t_i)_+}{d_i-t_i}
 =\frac{\mathbb E[(R_i-d_i)\mathbf1_{R_i>t_i}]}{(d_i-t_i)^2}
 \ge0.
 \tag{ST4}
\]
The displayed formula is the right derivative at \(d_i-1\). Every
contributing integer \(R_i\) is at least \(d_i\).

Increasing \(t_i\) increases every tail of \(K_i\), including the
saturated tails. Common-quantile coupling makes this run increase while
all other independent runs stay fixed. Every future \(R_j\), and its
hinge with fixed threshold \(t_j\), is nondecreasing in \(K_i\).
Hence future charges do not decrease either; earlier charges are
unchanged. Lowering any \(t_i>d_i-1\) to \(d_i-1\) cannot increase
the full objective. Applying this to all six coordinates reduces the
domain to \(0\le t_i\le d_i-1\).

### The whole future cost is affine in a single cap

In this smaller box, \(C_i\le p_i-1<p_i\), so saturation disappears.
The exact atom probabilities are
\[
 \Pr(K_i=0)=1-C_i/p_i,\qquad
 \Pr(K_i=k)=C_i\frac{p_i-1}{p_i^{k+1}}\quad(k\ge1).
 \tag{ST5}
\]
With other thresholds fixed, condition a future charge on \(K_i=k\)
and integrate the other runs. The resulting nonnegative function of
\(k\) grows at most linearly in \(k+1\): its load contains exactly
one factor \(1+K_i\), and the other factors have finite mean.
Its expectation under (ST5) is therefore an absolutely convergent
affine function of \(C_i\). The sum of all future charges has the same
property. Independence and deterministic thresholds are used here.

For \(t_i\in[k,k+1]\), integrality of \(R_i\) gives
\(\mathbb E(R_i-t_i)_+=A-Bt_i\), including both endpoint values.
Since \(C_i=(p_i-1)/(d_i-t_i)\), the whole objective on this interval
has the form
\[
 S(t)=A'+\frac{B'}{d_i-t_i}.
 \tag{ST6}
\]
Its derivative has a fixed sign, or is zero. At least one integer
endpoint is no worse. Starting from a real vector, move one coordinate
at a time to such an endpoint, with the others held at their current
values. After six moves the cost has not increased and
\[
 t_i\in\{0,1,\ldots,p_i-3\}.
 \tag{ST7}
\]
Every real point is thus dominated by a grid point, and the grid is part
of the real domain. Their minima agree exactly. Joint convexity is not
assumed. The local fractional-linear threshold mechanism already appears
in [Chapter 03](03-adaptive-kernels-lower-the-unrestricted-cutoff-to-19.md);
the present reduction includes the entire future cost of this fixed
six-prime schedule.

## 2. Exact evaluation retains every height

For an integer-valued \(Y\ge1\) and integer \(T\ge1\),
\[
 \mathbb E(Y-T)_+=\mathbb EY-T+
        \sum_{n=1}^{T-1}(T-n)\Pr(Y=n).
 \tag{ST8}
\]
All high products remain in the full mean. The root distribution is
\[
 \Pr(1+K_0=1)=\frac13,\quad
 \Pr(1+K_0=n)=\frac4{3^n}\ (n\ge2),\quad
 \mathbb E(1+K_0)=2.
\]
At a grid threshold put \(\beta=p-2-t\). Equation (ST5) gives
\[
 \begin{aligned}
 \mathbb E(1+K_p)&=1+1/\beta,\\
 \Pr(1+K_p=1)&=1-\frac{p-1}{\beta p},\\
 \Pr(1+K_p=n)&=\frac{(p-1)^2}{\beta p^n}\quad(n\ge2).
 \end{aligned}
 \tag{ST9}
\]
The largest required \(T=t+1\) is 17. Exact probabilities of products
1 through 16, together with the exact full mean, therefore determine
every grid charge. Multiplying low-product laws computes these
probabilities exactly: a discarded product cannot return below 17,
because every later factor is at least one. The producer evaluates the
hinges by the equivalent recurrence
\[
 h_1=\mathbb EY-1,\qquad
 h_{T+1}=h_T-1+\Pr(Y\le T).
 \tag{ST10}
\]

The grid has
\(3\cdot5\cdot9\cdot11\cdot15\cdot17=378675\) points. The
exact minimum is (ST1); its excess over one is
\[
 \frac{96812339801443376734222122601607917471999427}
      {37918700535989642067334158824877050925450000000}>0.
 \tag{ST11}
\]
The second-smallest grid objective, at \((0,1,3,5,7,8)\), is
\[
 \frac{41889130937052343408811707617568867646869}
      {41780315863536803711730356582620009687500},
\]
strictly larger. Every grid objective is evaluated as a Fraction; no
rounding direction or numerical tolerance is involved. The certificate
retains both exact schedules and their six exact stage costs, and counts
all 378,675 objectives as strictly greater than one. Section 1 supplies
the real-parameter quantifier; the computation supplies the exact finite
minimum.

Any probability mixture of complete deterministic schedules has average
ledger cost at least (ST1). Appending later nonnegative charges while
retaining this fixed prefix also cannot restore a positive reserve.
Neither deduction covers a policy whose thresholds depend on the actual
history, or an estimate retaining relationships discarded by (ST3).

## 3. Existing actual-label colors and their boundary

The congruence specialization of
[Chapter 16](16-canonical-conflict-resampling-and-the-exact-shearer-query-ratio.md#congruence-and-complete-layout-specialization)
already gives the following reduction. Delete any original class
contained in another remaining class. The finite procedure preserves
the covered set exactly, with no residue moves or modulus replacement.
In the retained family, distinct comparable numerical moduli have
disjoint classes: if \(m\mid n\), compatibility would imply
\(A_n\subseteq A_m\).

Fix a current prime \(q\), exponent \(a\ge1\), and a complete earlier
word \(x\). Among retained labels \(q^an\), with every prime factor of
\(n\) among the earlier coordinates, whose earlier cylinders contain
\(x\), color each complete cofactor by its original residue
modulo \(q^a\). Comparable distinct active cofactors cannot have the
same color. Each color is therefore a divisor antichain, and the active
cofactors form a union of \(q^a\) antichains. The colors are fixed
across all histories. In particular, for a chain of \(q^a+1\) distinct
retained cofactors at this exponent,
\[
 \prod_{\ell\text{ in the chain}}
       \mathbf1_{A^{\mathrm{earlier}}_\ell}(x)=0
 \quad\text{for every actual earlier word }x.
 \tag{ST12}
\]
This is Chapter 16's fact applied to a fibre, followed by pigeonhole;
it is not a new antichain theorem or a claim of generic negative
correlation for incomparable labels.

The restriction to retained labels is essential. The distinct odd
classes \(0\pmod{5\cdot3^j}\), \(j=0,\ldots,5\), have six
cofactors simultaneously active at the earlier 3-adic word zero for
\(q=5,a=1\). Their product of earlier indicators is one. Containment
reduction retains only \(0\pmod5\); the reduced-family zero cannot
be inserted into a load which still counts all six original labels.

In a finite exponent box \(0\le e_j\le k_j\), the classical
symmetric-chain decomposition bounds a union of \(r\) antichains by
the sum of the \(r\) largest coefficients of
\(\prod_j(1+z+\cdots+z^{k_j})\). Each symmetric chain of length
\(L\) contributes at most \(\min(r,L)\), attained by the \(r\)
central ranks, proving this count. For \(q=5,a=1\) and eight Boolean
coordinates the bound is
\[
 \binom82+\binom83+\binom84+\binom85+\binom86=238.
\]
This bound is attained by a real reduced odd family. The coordinate
order in this example differs from Sections 1--2: prime 5 is processed
after the eight displayed cofactor primes. Use earlier primes
\(3,7,11,13,17,19,23,29\), retain Boolean cofactors of ranks 2 through
6, and give each class zero earlier residues and current 5-residue
\(\mathrm{rank}-2\). Moduli are distinct; comparable cofactors have
different current residues and hence disjoint full classes. At earlier
word zero exactly 238 are active. This is a pointwise count example,
not a cover or a uniform positive-mass estimate.

A count constraint cannot be imposed after a nesting comparison by
clipping its output. Two disjoint events of probability one-half have
actual count one. Their nested comparison count is zero or two with
equal probabilities; clipping at one lowers its mean to one-half.
The comparison would then have the wrong direction. A stronger
continuation must preserve the same retained labels, fixed colors and
actual earlier-prefix intersections under one law during the comparison.
The scalar obstruction and the sharp count bound do not provide the
uniform quantitative saving needed for unrestricted Erdős #7.

## 4. Portable exact certificate

[`scalar_threshold_barrier_certificate.py`](../frontier/cover-geometry/scalar_threshold_barrier_certificate.py)
uses Python 3.10 or later and only the standard library. It checks the
entire grid, its strict barrier and the separated exact minimum and
runner-up. Checks remain enabled under `-O`. Its deterministic
[`JSON certificate`](../frontier/cover-geometry/scalar_threshold_barrier_certificate.json)
contains no timestamps, paths or elapsed times. No external data file,
source verifier, optimizer, geometry cache or Lean process is used.

From any working directory, including `/`, run with absolute paths:

```sh
python3 -I -S /path/to/trureturing/docs/reports/erdos7-odd-covering/frontier/cover-geometry/scalar_threshold_barrier_certificate.py --output /tmp/scalar_threshold_barrier_certificate.json
```

The only input is the fixed mathematical model embedded in the producer.
Its input digest is the SHA-256 of the JSON `model` object encoded as
UTF-8 with sorted keys, separators `(',', ':')`, and one final LF. The
producer also records its own source digest. The supplied identities are:

| Object | SHA-256 |
|---|---|
| Canonical model input | `ca3cc2d12a092c9986de004c625be38a3872da939cfdc2459492992d66b76128` |
| Producer | `faec7c1bb25aaa8f344e5661285f49de75ccd38e3abdebe9e31493e9e9443022` |
| Deterministic JSON | `80b562fc55fce3a3eba5a0422511205c8f3727da3542ab01bc25f6c11af07a3e` |

The arithmetic certifies this defined comparison expression. The
continuous reduction, actual-family coloring application and its
counterexamples are the ordinary arguments above; neither a finite
grid nor the JSON alone establishes those mathematical bridges.
