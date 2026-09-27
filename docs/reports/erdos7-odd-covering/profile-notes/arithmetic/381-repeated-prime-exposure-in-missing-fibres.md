[Index](../../marked_head_profile.md) · [Prime-flat construction](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md) · [Original extremal family](../321-384/350-extremal-paired-branch-and-source-support.md) · [Missing-fibre quotient and Haar costs](380-small-prime-survivors-and-original-haar-costs.md)

# Repeated composites or exposed prime squares in missing fibres

The whole quotient on a saturated missing 5-fibre has numerical
multiplicity at most two. Either a composite quotient modulus repeats,
or a repeated prime must divide an original surviving quotient modulus
to exponent at least two, with that class reaching outside the union of
all repeated-prime classes. A square hidden inside one of those prime
classes does not supply this obstruction.

The proof first deletes classes contained in the repeated-prime union,
then iterates the prime-flat construction already proved in report 348.
This preserves the other repeated primes and their flatness until all
repetitions have disappeared, which Hough--Nielsen forbids for a cover
with every modulus coprime to 6. The resulting alternative is a
repo-derived ordinary deduction, not a new Lean theorem or a claim of
literature novelty.

The residue condition is stronger than an original height bound.
Explicit partial families below also show that the alternative and the
listed local original-family properties do not by themselves force a
uniform positive composite cost relative to pure-survivor mass.
Those families are not whole covers and do not have a saturated
first-5 projection.

## 1. The actual quotient and its repeated original pairs

Use the hypothetical extremal odd cover of
[350, EB1--EB3](../321-384/350-extremal-paired-branch-and-source-support.md).
Its original classes are \(A_d=a_d\bmod d\), \(d\in D\), with distinct
odd \(d>1\), full period \(Q=\prod_{p\in\Lambda}p^{H_p}\), and
normalized prime classes \(A_p=0\bmod p\). The original set \(D\) is
divisor-closed above one, and comparable original classes are disjoint.

Assume the three-root first-5 branch of
[378](378-saturated-prime-fibres-and-mixed-tail-incidence.md).
Put \(B=Q/3^{H_3}\), let \(v\ne0\bmod5\) be the missing first-5 root
of the actual 3-free residual, and write
\(F_v=\{x\bmod B:x\equiv v\bmod5\}\).
[380, HB5--HB7](380-small-prime-survivors-and-original-haar-costs.md)
restricts the original 3-free classes to a whole cover \(\mathcal C_v\)
of this fibre. On a cyclic carrier of order \(B/5\), an active original
has quotient modulus

\[
 m(d)=
 \begin{cases}
 d,&5\nmid d,\\
 d/5,&5\mid d,
 \end{cases}
 \qquad
 \text{activity means }5\nmid d\text{ or }a_d\equiv v\pmod5.
 \tag{RE1}
\]

All these quotient moduli exceed one and are coprime to 6.
The only numerical repetitions are pairs of original labels

\[
 r,5r\in D,\qquad (r,30)=1,\qquad a_{5r}\equiv v\pmod5.
 \tag{RE2}
\]

Their two quotient residues modulo \(r\) are different. Define
\(\mathcal R_v\) to be the set of these repeated bases. It is nonempty:
otherwise the quotient would be a distinct odd whole cover with fewer
classes than the original minimum.

If every \(r\in\mathcal R_v\) is prime, put
\(\mathcal P_v=\mathcal R_v\) and
\[
 b_p=a_{5p}\bmod p\ne0\qquad(p\in\mathcal P_v).
 \tag{RE3}
\]
In original CRT coordinates on the fibre, the two repeated-\(p\)
classes are exactly the roots \(0,b_p\bmod p\).
The affine parametrization \(x=v+5z\) changes all these residues by the
same invertible affine map modulo \(p\), so membership and nonmembership
in these two roots are preserved.

## 2. Delete covered classes before testing prime flatness

Consider any finite whole cover \(\mathcal C\) with all moduli greater
than one and coprime to 6, with numerical multiplicity at most two.
Remove identical copies of a congruence class first. Suppose that no
composite numerical modulus repeats. Let \(\mathcal P\) be its set of
repeated prime moduli, each with two distinct residues, and let \(U\)
be the union of all those repeated-prime classes.

The set \(\mathcal P\) is nonempty. Otherwise the cover is distinct,
contrary to
[Hough--Nielsen, Theorem 1](https://arxiv.org/pdf/1703.02133v2):
every finite distinct covering with moduli greater than one has a
modulus divisible by 2 or 3.

Retain all repeated-prime classes. Delete every other class contained
in \(U\). This preserves whole coverage. For a class \(a\bmod m\),
containment in \(U\) occurs exactly when some \(p\in\mathcal P\)
divides \(m\) and \(a\bmod p\) is one of that prime's two repeated
residues. One implication is immediate. For the other, if none of the
fixed prime roots lies in its repeated pair, prescribe an outside root
at each \(p\in\mathcal P\) not dividing \(m\). Since \(p\ge5\), such a
root exists; CRT with \(x\equiv a\bmod m\) gives a point outside \(U\).

We prove the following alternative:

\[
 \begin{gathered}
 \text{a composite numerical modulus repeats, or}\\
 \exists p\in\mathcal P,\ \exists(a\bmod m)\in\mathcal C:
       \quad p^2\mid m,\qquad (a\bmod m)\setminus U\ne\varnothing.
 \end{gathered}
 \tag{RE4}
\]

The convention about identical copies applies before defining
\(\mathcal P\) and \(U\). The actual quotient in section 1 already has
different residues at every repeated modulus and needs no such deletion.

Suppose the second alternative fails after the first has been excluded.
Every class remaining after the deletion is then \(p\)-flat for every
repeated prime \(p\): no remaining modulus is divisible by \(p^2\).
The next construction eliminates these repetitions one at a time.

## 3. Eliminate one repeated prime while preserving the others

Fix a repeated prime \(p\) in the current cover, assumed \(p\)-flat.
Permute its first-digit coordinate to send its two repeated classes to
\(0,1\bmod p\), keeping all other CRT coordinates unchanged. Because
the current \(p\)-height is one, this preserves every class's modulus
and all covering memberships.

Keep the \(p\)-free classes, denoted \(\mathcal S_p\).
Delete any other classes contained in roots 0 or 1.
Every remaining \(p\)-bearing modulus has the form \(pm\), where
\(p\nmid m\) and \(m>1\). Its first \(p\)-root
\(\xi\) belongs to \(\{2,\ldots,p-1\}\).
Let \(\mathcal T_\xi\) consist of the corresponding classes modulo
\(m\), with their original cofactor residues.

For every \(\xi\), the family
\(\mathcal S_p\cup\mathcal T_\xi\) covers the \(p\)-free carrier.
Indeed, prescribe that cofactor state and first \(p\)-root \(\xi\)
in one original point and use the current whole coverage.
Across all \(\mathcal T_\xi\), the numerical moduli \(m\) are distinct:
the inputs \(pm\) are composite and therefore occur only once.
The retained \(p\)-free list may still contain other repeated primes.

Choose a fresh prime \(q\ge5\) dividing no current modulus. Keep
\(\mathcal S_p\) and add the following classes, exactly as in
[348, section 2](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md):

1. \(p^i\bmod p^{i+1}\), for \(0\le i\le q-2\).
2. For each \(a\bmod m\in\mathcal T_\xi\) and \(0\le i\le q-2\),
   the CRT class
   \[
     x\equiv \xi p^i\pmod{p^{i+1}},\qquad
     x\equiv a\pmod m.
   \]
3. The closing class
   \[
     x\equiv0\pmod{p^i},\qquad x\equiv i\pmod q
   \]
   for each \(0\le i\le q-1\), with the modulus-one first condition
   vacuous at \(i=0\).

This covers every integer. If \(p^{q-1}\nmid x\), let
\(i=v_p(x)<q-1\). First nonzero \(p\)-digit 1 is covered by family 1.
For first nonzero digit \(\xi\ge2\), the cover
\(\mathcal S_p\cup\mathcal T_\xi\) supplies family 2 or a retained
\(p\)-free class. If \(p^{q-1}\mid x\), take the representative
\(i=x\bmod q\) in \(\{0,\ldots,q-1\}\); then \(p^i\mid x\) and the
corresponding closing class covers it. This includes \(x=0\).

The new modulus types are \(p^{i+1}\), \(p^{i+1}m\), and \(p^iq\).
They are mutually distinct: \(p\nmid m\), \(m>1\), all such \(m\)
are distinct, and fresh \(q\) divides none of them. They do not collide
with the retained \(p\)-free moduli; the only new \(p\)-free modulus
is \(q\), which is fresh.

Thus \(p\) is no longer repeated, and the other repetitions remain
exactly the other repeated primes. For an untreated repeated prime
\(r\), every old modulus was \(r\)-flat. The new ones multiply old
cofactors only by powers of \(p\), or use \(p^iq\), with \(r\ne p,q\).
Consequently no square of \(r\) has been introduced.

There are finitely many repeated primes. Repeating this operation
therefore gives a distinct whole cover with all moduli still coprime
to 6, contradicting Hough--Nielsen. This proves RE4.
The witness in RE4 belongs to the family before any surgery: the
contradiction started by assuming the already pruned original family
was flat at every repeated prime.

The square-free input theorem of
[Harrington--Sun--Wong, Theorem 3.2](../../../../../Library/Arith/harrington2021oddcovering.md)
is not being applied with weakened hypotheses. Report 348 already
proves the construction under the sufficient \(p\)-flat premise.
Here its proof is reused with other repeated primes in the retained
\(p\)-free list, and the preservation argument justifies iteration.

## 4. The exposed square is an aligned original label

Apply RE4 to \(\mathcal C_v\). It gives the following necessary
condition on the actual saturated branch:

\[
 \begin{gathered}
 \exists r\in\mathcal R_v\text{ composite},\quad\text{or}\\
 \exists p\in\mathcal P_v,\ \exists d\in D:
 \quad 3\nmid d,\quad p^2\mid d,\quad
 \bigl(5\nmid d\ \text{or}\ a_d\equiv v\pmod5\bigr),\\
 \qquad a_d\bmod r\notin\{0,b_r\}
       \quad\text{for every }r\in\mathcal P_v\text{ dividing }d.
 \end{gathered}
 \tag{RE5}
\]

The second case is considered when all repeated bases are primes.
Division by 5 does not change any repeated prime's valuation, since
each \(p\in\mathcal P_v\) is coprime to 30. The activity clause in RE5
retains the exact original first-5 alignment.
By the CRT argument in section 2, these residue conditions say that
the restricted original class has a point outside the union of every
repeated-prime class on the fibre.

In particular the witnessing original satisfies

\[
 p^2\mid d,\qquad a_d\bmod p\notin\{0,b_p\}.
 \tag{RE6}
\]

Comparable-original disjointness already excludes root zero.
The additional information is exclusion of the root of the actual
original \(A_{5p}\).

An original height \(H_p\ge2\) alone gives less. Divisor closure puts
\(p^2\) in \(D\), and its pure original class necessarily meets \(F_v\)
because \(p\ne5\). But its first \(p\)-root may be \(b_p\), in which
case this active square class lies inside the repeated-\(p\) union
and is deleted before the flatness test.

## 5. Existing interval and multiplicity bounds on repeated pairs

Let \(k\) be the number of singleton classes in \(\mathcal C_v\), and
let \(\delta\) be their uncovered density on the quotient's own
periodic carrier. Those singleton classes cannot cover: they are
distinct and coprime to 6. The standard interval theorem reused in
[357](../321-384/357-original-private-swaps-and-prime-reset-transport.md)
says a noncovering family of \(k\) APs cannot cover \(2^k\) consecutive
integers. Counting cyclic windows gives \(\delta\ge2^{-k}\).
The paired classes cover this residual, so

\[
 \sum_{r\in\mathcal R_v}\frac1r\ge\frac{\delta}{2}
       \ge2^{-(k+1)},\qquad
 \sum_{r\in\mathcal R_v}\left(\frac1r+\frac1{5r}\right)
       \ge\frac35\,2^{-k}.
 \tag{RE7}
\]

The factor distinguishes quotient pair mass \(2/r\) from original
pair mass \(6/(5r)\); no survivor law is exchanged.

There is also a bound on a repeated base in terms of \(k\) alone.
Translate every paired quotient class by \(-t\), \(0\le t<2^k\).
For each integer \(y\), some \(y+t\) avoids all singleton classes
and hence belongs to a paired class. These translates therefore form
a whole cover, whose numerical moduli are precisely repeated bases
and whose multiplicity is at most \(2^{k+1}\).

[Klein--Koukoulopoulos--Lemieux, Theorem 3 and Definition 2.2,
arXiv:2212.01299v2, p. 3](https://arxiv.org/pdf/2212.01299v2)
bound the least modulus of a cover of multiplicity \(s\) by
\(\exp(c\log^2(s+1)/\log\log(s+2))\), for an absolute constant \(c\).
Applying that published theorem to the auxiliary translated cover gives

\[
 \min\mathcal R_v\le
       \exp\!\left(\frac{C(k+1)^2}{\log(k+2)}\right)
 \tag{RE8}
\]

for an absolute constant \(C\). The auxiliary translations do not
change the numerical repeated bases or assert an original-Haar
transport. These direct deductions supply no explicit small-prime
cutoff when \(k\) is unrestricted.

## 6. Exact partial families delimit the qualitative conclusion

Fix any prime \(p\ge7\). For every odd prime \(r\le p\), take the
original class \(0\bmod r\), and add

\[
 A_{5p}=1\bmod5p,\qquad A_{p^2}=\varepsilon\bmod p^2,
       \qquad\varepsilon\in\{1,2\}.
 \tag{RE9}
\]

The numerical moduli are distinct odd nonunits and divisor-closed
above one. Their support is an initial segment of odd primes, with
height two at \(p\) and height one elsewhere. All comparable classes
are disjoint.

Both families are irredundant. For a prime label \(r\), prescribe its
coordinate zero, all other prime coordinates nonzero, and, if \(r\ne p\),
the full \(p\)-coordinate \(3\bmod p^2\). This gives a private point
by CRT. For \(A_{5p}\), use first-5 root 1 and
\(p\)-coordinate \(1+p\bmod p^2\), keeping other prime coordinates
nonzero. For \(A_{p^2}\), use its prescribed \(p\)-coordinate and
first-5 root 2, again keeping all other prime coordinates nonzero.

On first-5 root 1, the 3-free restricted family has exactly one
repeated numerical modulus, namely \(p\), with roots 0 and 1.
When \(\varepsilon=1\), the active square class lies inside repeated
root 1. Thus height two and activity do not imply exposure.
When \(\varepsilon=2\), that square class is outside both repeated
roots. The exposed-square alternative is then satisfied by one
arbitrarily large repeated prime at height two.

These are partial families. For every nonzero first-5 root, prescribe
the \(p\)-coordinate \(3\bmod p^2\) and every other 3-free prime
coordinate nonzero. The resulting point avoids all 3-free classes.
Hence the actual first-5 projection of \(R_3\) has four roots in both
families. Also taking the first-3 coordinate nonzero gives an
uncovered point of the full original family. Neither is a whole
cover or a saturated-branch example.

Their repeated-original-pair reciprocal mass is \(6/(5p)\), and
their entire original composite reciprocal mass is
\(1/(5p)+1/p^2\). The numerical coefficient \(c_d\) from
[361, PR5](../321-384/361-prime-overlap-reservation-for-composite-parents.md)
lies in \([0,1]\), so for these partial families

\[
 0\le M_{\mathrm{comp}}\le\frac1{5p}+\frac1{p^2},
 \qquad
 X=\left(1-\frac1{p(p-1)}\right)
       \prod_{\substack{r\le p\\r\text{ odd prime}}}
                         \left(1-\frac1r\right).
 \tag{RE10}
\]

The ratio \(M_{\mathrm{comp}}/X\) also tends to zero. To see this
without a prime-distribution estimate, write \(n=(p-1)/2\).
Since all factors lie in \((0,1)\),

\[
 \prod_{\substack{r\le p\\r\text{ odd prime}}}(1-1/r)
 \ge\prod_{j=1}^{n}\frac{2j}{2j+1}
 \ge\frac1{\sqrt{2n+1}}=\frac1{\sqrt p}.
 \tag{RE11}
\]

The second inequality follows by induction from
\((2j+2)^2>(2j+1)(2j+3)\).
Consequently \(X\ge41/(42\sqrt p)\), and RE10 proves the claimed
vanishing ratio.

Thus the exposed-square restriction together with these local
divisor, disjointness, support, height and private-point properties
does not force a uniform positive relative composite cost.
The no-prime coverage condition in
[361, PR6](../321-384/361-prime-overlap-reservation-for-composite-parents.md),
and hence the uniform floor \(M_{\mathrm{comp}}>X/140\) in
[380](380-small-prime-survivors-and-original-haar-costs.md), are absent
from these controls.

## 7. Remaining scope

RE5 locates an actual original repeated composite pair or an aligned
square-bearing original outside the repeated-prime union. It does not
force the repeated base to involve 7 or 11, does not bound the number
of singleton quotient classes, and does not supply an upper bound on
the original composite budget.
An unrestricted contradiction still requires additional joint
coverage information or an incompatible upper bound on the same
original-Haar quantity. None is established here.
