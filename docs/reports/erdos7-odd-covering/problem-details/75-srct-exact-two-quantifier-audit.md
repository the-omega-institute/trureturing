[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# SRCT: the exact-two-9 implication and a repeated-layer counterexample

The SRCT exact-two-9 claim would imply the unrestricted distinct odd-covering
conjecture. However, the universal repeated-layer gain bound in its current
proof fails on an explicit congruence calculation. This audit rejects that
proof step, without deciding whether the claimed nonexistence theorem is true.

## External source and verification scope

The source is the public
[Shunyaya Residual Capacity Theory repository](https://github.com/OMPSHUNYAYA/Shunyaya-Residual-Capacity-Theory)
at revision 95531a4849fdd0a072e5cf943abd96ac7fe136bf. Its theorem manuscript is
[version 1.15.43](https://github.com/OMPSHUNYAYA/Shunyaya-Residual-Capacity-Theory/blob/95531a4849fdd0a072e5cf943abd96ac7fe136bf/01_Theorem_and_Proof/SRCT_Modulus9_Exactly_Twice_Obstruction_Theorem_v1_15_43.md),
with SHA-256

    eb10e4b26afdff144774a3f56e2f060d78319bf228f3fd7f3be30e9aad032d7e

The source states: no finite covering has all moduli odd and greater than
$1$, modulus $9$ exactly twice, and every other modulus at most once.
It explicitly assumes neither irredundancy nor distinct residues for the two
$9$-classes.

Both source checks were reproduced: 556/556 self-test and 565/565 repository
verification, with exit code zero. The source describes its universal lemmas
as not proof-assistant formalized. The passing checks do not validate the
universal gain claim against arbitrary congruence realizations. This audit's
two independent standard-library programs import no SRCT code.

## Exact-two-9 nonexistence would imply Erdős #7

Let $C$ be any finite covering with pairwise distinct odd moduli $m_i>1$.
Since the moduli are distinct, $9$ occurs zero or one time.

- If $9$ is absent, adjoin $0\bmod9$ and $1\bmod9$.
- If $9$ occurs once, with residue $a\bmod9$, adjoin $(a+1)\bmod9$.

Adding classes preserves coverage. Every non-$9$ modulus still occurs at most
once, and $9$ now occurs exactly twice. Thus

\[
\exists C\;\mathrm{DistinctOddCover}(C)
\ \Longrightarrow\
\exists C'\;\mathrm{ExactTwo9OddCover}(C').
\]

Contrapositively, the declared exact-two nonexistence theorem would settle the
unrestricted distinct odd-covering problem. The source README's assertion
that multiplicities zero and one remain outside the conclusion is incompatible
with this implication. Section 13's separate augmentation by the canonical
modulus $K$ does not block augmentation by $9$.

The checker
[verify_srct_exact_two_e7_implication.py](../verify_srct_exact_two_e7_implication.py)
tests all 23,040 residue assignments over subsets of $\{3,5,7,9,11\}$.
Every transformed family satisfies the exact-two class restrictions and retains
every original class. This is a bounded regression of the transformation;
the universal implication follows from the case split above.

## A literal repeated-layer counterexample to Lemma 9.2

Use the source's own core and support constants:

\[
B=51975=3^3\,5^2\,7\,11,\qquad K=221B,\qquad
\theta_0=\frac{221}{192},\qquad R_0=\frac7{48}.
\]

For a residual set $W\subseteq\mathbb Z/M\mathbb Z$, define the actual
divisor capacities and deficit exactly as in Sections 4 and 7 of the source:

\[
C_W(d)=\max_{a\bmod d}|\{x\in W:x\equiv a\pmod d\}|,\qquad
S(W)=\sum_{d\mid M}C_W(d),
\]
\[
D(W)=|W|-\sum_{\substack{d\mid M\\d\notin E}}C_W(d).
\]

Here $E$ contains the forbidden identity label and all already used modulus
labels. The two used $9$-classes leave no further available modulus-$9$ label.

The core parent residual set is

\[
U=\{x\bmod B:x\not\equiv0\pmod p\ (p=3,5,7,11),\
x\not\equiv1,2\pmod9\}.
\]

For the core child, take the class $4\bmod27$:

\[
V=U\setminus\{x:x\equiv4\pmod{27}\}.
\]

The parent exclusion set is $E=\{1,3,5,7,9,11\}$; the child adds $27$.
Direct residue counting gives:

| Core state | Active mass $A$ | Raw capacity sum $S$ | Deficit $D$ |
| --- | ---: | ---: | ---: |
| Parent $U$ | 14,400 | 44,044 | 2,996 |
| Child $V$ | 13,200 | 42,042 | 3,178 |

The source's renewal shape is therefore

\[
(u,X,Y,G)=(0,182,802,1200),
\]

where $G=A-A'$, $u=C_U(27)-G$, $X$ sums the decreases of the other
available capacities, and $Y=S-S'-G$.

Now append two repeated $3$-adic layers. Put $B_2=9B=467775$ and
$L=221B_2=103378275$. Lift the parent constraints to $B_2$, but take the
localized class $4\bmod243$ for the child. This class projects through

\[
4\bmod243\ \longmapsto\ 4\bmod81\ \longmapsto\ 4\bmod27.
\]

Each step fixes one new $3$-adic digit, exactly the top-layer localization in
Lemma 8.1. The high-level child exclusion set adds $243$, not $27$.
Direct counting over $B_2$ gives:

| High-resolution state | Active mass $A$ | Raw capacity sum $S$ | Deficit $D$ |
| --- | ---: | ---: | ---: |
| Parent | 129,600 | 404,404 | 18,956 |
| Child after $4\bmod243$ | 128,400 | 402,402 | 19,138 |

The same renewal shape $(0,182,802,1200)$ is obtained from this table.
In particular, the localized class removes 1,200 points, not nine times
that number.

Restore the normalized zero classes for $13$ and $17$. Their coprime
coordinates give, directly by CRT divisor-capacity summation,

\[
D_{221}=192D+28A-29S.
\]

Indeed, the unrestricted support multiplier is
$(12+1)(16+1)=221$, the active multiplier is $12\cdot16=192$,
and the two newly excluded prime labels have total capacity $28A$.
Consequently,

\[
D_{\rm parent}=-4459364,\qquad
D_{\rm child}=-4399962,\qquad
\boxed{\Delta D_{\rm true}=59402}.
\]

These negative absolute deficits do not assert coverage. They are legitimate
residual-capacity states for testing a universal claim about gain.

Lemma 9.2 asserts $\Delta D_{\rm true}\ge F C_{\rm dec}$ for a renewal
shape and a finite sequence of layers. For the two repeated layers,
$b_1=b_2=3$ and

\[
F=192\cdot9=1728,\quad
U_{\rm model}=\frac{221}{192}\left(\frac43\right)^2-1,\quad
R_{\rm model}=\frac7{48}+\frac23.
\]

Its prescribed decoration charge is

\[
C_{\rm dec}
=182+802\,U_{\rm model}-1200\,R_{\rm model}
=\frac{2491}{54}.
\]

Thus the asserted lower bound becomes

\[
\boxed{59402\ \ge\ 79712},
\]

which fails by exactly 20,310. The source lists no terminal-only, positive-parent-
deficit, or restricted-branch premise in Lemma 9.2. If such a restriction is
intended, it requires a new statement and proof, together with a verified
application to Propositions 10.1 and 11.1.

## Why the envelope argument does not prove a gain bound

A pointwise capacity envelope can give $D_{\rm true}(W)\ge D_{\rm env}(W)$
for each state. Writing the difference as a nonnegative shadow $s(W)$ gives

\[
\Delta D_{\rm true}
=\Delta D_{\rm env}+s(W_{\rm child})-s(W_{\rm parent}).
\]

Nonnegativity of both shadows does not establish the required inequality
between their increments. Lemma 8.2 supplies a single-family nonnegative
shadow, without the needed monotonicity under the same actual TAKE.
There is also a scale mismatch when a fully lifted core TAKE is replaced by
one localized high-digit class, as the active masses above demonstrate.

The source's function named charge_envelope_challenge in its version 1.15.43
referee certificate compares two expressions built from the same abstract
product weights. It does not independently compute the true capacities for
this repeated-layer congruence example. Its passing result therefore does
not contradict this counterexample.

The independent checker
[srct_repeated_layer_counterexample.py](../frontier/cover-geometry/srct_repeated_layer_counterexample.py)
enumerates actual residues and divisor capacities for the core and the
two-layer instance. It also checks a core-supported TAKE under eight repeated
layers, using exact CRT fiber multiplicities; that control distinguishes the
failure from merely choosing the wrong localized interpretation.

For that control the same numerical class $1\bmod15$ is taken before and
after refinement. Its core shape is $(0,30,510,1800)$. At
$L=K\cdot3^8=75362762475$, direct sums of the original numerical labels give
$\Delta D_{\rm true}=146638350$, while $F C_{\rm dec}=404608800$.
The claimed lower bound exceeds the true gain by 257,970,450. In this control
the used label is unchanged, so the failure cannot be attributed to replacing
$27$ by $243$ or to excluding the projected label instead of the actual label.

## Reproduction and boundary

    python3 -I -O docs/reports/erdos7-odd-covering/verify_srct_exact_two_e7_implication.py
    python3 -I -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/srct_repeated_layer_counterexample.py

Both programs use explicit failures that remain active with Python
optimization enabled. They retain no external source code or finite
covering candidate.

This is an ordinary mathematical audit backed by exact integer/rational
computation, not a Lean-certified theorem. It invalidates the stated universal
gain bound and the present proof's use of that bound. It neither constructs an
odd distinct covering nor proves its impossibility. Unrestricted Erdős #7
remains open; the earlier finite-LCM and conditional source results retain
their previous scopes.
