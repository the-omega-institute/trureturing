---
bibkey: assani2025robinkaneko
authors: Idris Assani; Aiden Chester; Alex Paschal
year: 2025
title: On Robin's Inequality and the Kaneko-Lagarias Inequality
doi: null
url: https://arxiv.org/abs/2503.03159v2
claim: The paper gives elementary proofs of Robin safety for several large arithmetic classes and reduces the Kaneko-Lagarias test to superabundant numbers; its divisibility classes are not FIB additive inclusion classes.
strata_touched: []
license: citation-only
triage: anchor
---

# On Robin's Inequality and the Kaneko--Lagarias Inequality

The source is [arXiv:2503.03159v2](https://arxiv.org/pdf/2503.03159v2), updated 16 August 2025. The results below are attributed to that version; no independent proof audit or Lean verification is claimed.

The paper proves Robin's inequality for every $n>5040$ not divisible by any of $2,3,5$, for primorials above $30$, for sufficiently large $2^k m$ with $m$ odd, and for $21$-free integers. It also proves that the Kaneko--Lagarias inequality

$$
\sigma(n)<e^{H_n}\log H_n
$$

is equivalent to RH when checked on all integers, and that it is enough to check it on superabundant numbers. The paper explicitly leaves the analogous superabundant reduction for the full Lagarias inequality as future work.

## FIB interface and non-identification

The hypotheses here are divisibility and $p$-free conditions. A five-window state records additive inclusion of Fibonacci positions; labels such as $[2]$ or $[2\,5]$ do not assert $2\mid n$, $5\mid n$, or a prescribed $p$-adic valuation. Therefore the class results can be used only after an independent divisibility proof for a concrete FIB-generated integer. They do not supply the missing prime-support or same-price bridge for the general FIB family.


## Fixed valuation bounds and the actual GA2 source

The quantifier in Theorem 2.13 is important: it fixes the exponent of
$2$ and then makes the odd part sufficiently large. The stronger
Theorem 2.15 also gives an explicit exponent-dependent threshold. The
following application compares those sufficient conditions with the
same selected Robin source; it does not repeat either published proof,
claim a new general theorem, or supply a Lean verification.

### The thresholds in the primary text

In [arXiv:2503.03159v2](https://arxiv.org/pdf/2503.03159v2), printed
pp.5–6, write $N=2^k m$, with $m$ odd, and put
$A=\log N$, $L=\log A$. Equations (31)–(35) and Theorem 2.13 give the
sufficient condition

$$
L^2>\frac{2.51}{e^\gamma}(2^{k+1}-1).
\tag{V1}
$$

Equations (36)–(37) and Theorem 2.15 use the improved totient bound
and give

$$
L^3>\frac{0.0168}{e^\gamma}(2^{k+1}-1).
\tag{V2}
$$

For this latter application retain the stated domain of equation (36),

$$
N\ge C:=10^{10^{13.11485}}.
$$

The constants and totient estimate are literature inputs. Their
original proofs, computations and the finite verification used by
Theorem 2.16 are not repeated here. The selected source restriction
$A>10^{36}$ from the
[existing full-tail application](../Analytic/polak2026finiterobinca.md)
pays $N>C$: indeed
$\log C=(\log10)10^{13.11485}<3\cdot10^{14}<10^{36}$.
This preserves a condition needed by the proof even though the
printed Theorem 2.15 statement does not repeat it.

### Its actual exponent cannot meet these sufficient conditions

Keep the same conditional least integer $N>5040$ attaining the global
Robin-ratio maximum, with $A=\log N$ and $L=\log A$.
The existing [Caveney–Nicolas–Sondow selection](../Arith/caveney2012sacaga.md)
makes this integer GA2. Consequently its comparison with the actual
multiple $2N$ is valid; it does not require a deletion outside the
$N>5040$ domain or comparison with an independently chosen integer.

For its actual $k=v_2(N)$, the geometric factor in the divisor sum is

$$
\frac{Z(2N)}{Z(N)}
=\frac{2-2^{-(k+1)}}{2-2^{-k}}
=1+\frac1{2^{k+2}-2},
\qquad Z(n)=\frac{\sigma(n)}n.
$$

GA2 therefore implies

$$
\log\!\left(1+\frac1{2^{k+2}-2}\right)
\le\log\frac{\log(A+\log2)}{\log A}
<\frac{\log2}{A\log A}.
\tag{V3}
$$

The last step is the same concavity tangent used by the existing
source-price comparisons. Using $\log(1+x)\ge x/(1+x)$, $x>0$,
inside this application gives

$$
\boxed{2^{k+1}-1>\frac{A L}{2\log2}-\frac12.}
\tag{V4}
$$

For $L\ge26$, the existing elementary bounds
$\log2<1$, $e^\gamma<3$ suffice to compare (V4) with (V2).
The function $e^L/L^2$ is increasing for $L>2$, and
$e^{26}>2^{26}>1000\cdot26^2$, so $A>1000L^2$ on this range.
Hence

$$
\begin{aligned}
0.0168(2^{k+1}-1)
&>0.0084(AL-1)\\
&>8.4L^3-0.0084\\
&>3L^3>e^\gamma L^3.
\end{aligned}
\tag{V5}
$$

Thus the sufficient condition (V2) is false at this actual source
throughout the already relevant $L\ge26$ range. Condition (V1)
also fails, since $2.51>0.0168$ and $L>1$.
There is no assertion that Robin itself fails: a sufficient condition
being unavailable is not a converse to either theorem.

### What is and is not reused

The paper's fixed-$k$ safety result remains valid in its stated
families, and its density-one result remains a population statement.
The actual selected source has an exponent growing with its clock,
as witnessed by (V4); it cannot be included just by saying it is a
large even integer. This comparison closes the applicability question
for these two particular thresholds, not the original Robin target.
It neither excludes other uses of the paper nor improves a verified
zero height or a numerical source-clock restriction.

The complete signed $I_\psi(A)$ lower bound, or a paid bound on the
centered Gaussian response at this same $N$, is still missing.
No zero real part, multiplicity, fixed unverified band or infinite tail
has been removed. The first counterexample to another inequality is
not substituted for this global maximizing integer. The existing
FIB distinction between additive five-window inclusion and arithmetic
valuation also remains in force: (V4) uses an actual multiplication
comparison, not a label such as $[2]$.
