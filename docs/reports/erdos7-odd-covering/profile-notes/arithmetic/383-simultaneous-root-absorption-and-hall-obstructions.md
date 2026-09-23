[Index](../../marked_head_profile.md) · [Prime-flat construction](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md) · [Actual missing-fibre quotient](380-small-prime-survivors-and-original-haar-costs.md) · [Repeated-prime exposure](381-repeated-prime-exposure-in-missing-fibres.md)

# Simultaneous root absorption and Hall obstructions

A finite whole cover with numerical multiplicity at most two admits a
simultaneous elimination of repetitions touching a chosen set of odd
primes, provided two roots at each chosen prime absorb all relevant
prime-square classes and at least one copy of every relevant repeated
modulus. The absorption is tested against the union of all chosen
prime cylinders. A class hidden by a different chosen prime is removed
before the prime-flat construction is applied.

For a whole cover whose moduli are coprime to 6, Hough--Nielsen then
gives an alternative. Either the repeated numerical moduli cannot be
assigned distinct prime divisors, or every such assignment and every
compatible choice of root pairs exposes an original square-bearing
class outside the entire chosen union. If the primes needed for an
assignment are all flat in the original input, the assignment is
impossible. Hall's theorem expresses this as a strict deficiency of
available prime divisors.

These are ordinary deductions from CRT, the prime-flat construction in
report 348, and the published distinct-cover obstruction. They are not
Lean verification, a literature-novelty claim, or a resolution of
unrestricted Erdős #7. The constructions preserve whole coverage and
specified literal repetitions; they do not transport the original
probability law or reciprocal-cost budget.

## 1. A union of two-root cylinders

Let \(\mathcal C\) be a finite whole cover of the integers by classes
\(a\bmod m\), with \(m>1\) and each numerical modulus used at most
twice. Delete identical copies of the same class before identifying
the set \(\mathcal R\) of repeated numerical moduli. Each repeated
modulus then has two different residues. Let \(P\) be a finite set of
odd primes. Define

\[
 U_p=\{a\bmod p:(a\bmod p)\in\mathcal C\},\qquad
 R_p\subseteq\mathbb Z/p\mathbb Z,\quad |R_p|=2,
 \quad U_p\subseteq R_p\qquad(p\in P),
\]
\[
 V=\bigcup_{p\in P}\ \bigcup_{u\in R_p}(u\bmod p).
 \tag{SA1}
\]

For an original class \(A=a\bmod m\),

\[
 A\subseteq V
 \quad\Longleftrightarrow\quad
 \exists p\in P:\ p\mid m,\quad a\bmod p\in R_p.
 \tag{SA2}
\]

The reverse implication is immediate. For the forward implication,
suppose the condition on the right fails. For every \(p\in P\) not
dividing \(m\), choose a root outside \(R_p\); such a root exists
because \(p>2\). These choices and \(x\equiv a\pmod m\) have a
common solution by CRT. At selected primes dividing \(m\), its root
is already outside \(R_p\). The resulting integer belongs to
\(A\setminus V\), which proves the contrapositive.

Suppose the following two absorption conditions hold:

\[
 p\in P,\ p^2\mid m,\ A=(a\bmod m)\in\mathcal C
       \quad\Longrightarrow\quad A\subseteq V.
 \tag{SA3}
\]
\[
 r\in\mathcal R,\ \gcd(r,\prod_{p\in P}p)>1
       \quad\Longrightarrow\quad
       \text{at least one of its two classes lies in }V.
 \tag{SA4}
\]

Adjoin the two pure-prime classes at each \(p\in P\), and delete
every original class contained in \(V\). Call the resulting family
\(\mathcal C^*\). Coverage is preserved because the added classes
cover every deleted class. Its relevant properties are:

1. It is flat at every \(p\in P\): no modulus is divisible by
   \(p^2\), by SA3.
2. Its only repeated moduli touching \(P\) are the added pure primes
   \(p\in P\). Indeed SA4 removes at least one copy of each old
   repetition, while \(U_p\subseteq R_p\) removes every old pure-
   \(p\) class before the new pair is inserted.
3. Every old class whose modulus is coprime to \(\prod_{p\in P}p\)
   is retained literally, by SA2. Its repeated moduli and both of
   their residues are therefore unchanged.

The intermediate addition is an auxiliary enlargement. Its validity
does not require the added prime classes to be original labels.

## 2. Eliminate one flat repeated prime

The following form of the construction permits repetitions in the
retained \(p\)-free list. Assume a current whole cover has exactly two
pure-\(p\) classes, is \(p\)-flat, and has no other repeated modulus
divisible by \(p\). Permute its first \(p\)-coordinate to send those
two roots to 0 and 1, keeping every other full prime-power coordinate
fixed. Flatness makes this a bijection of the whole periodic carrier
that preserves AP moduli and covering membership.

Keep every \(p\)-free class; denote this list by \(\mathcal S\).
Delete any other class in root 0 or 1. Write the remaining classes as
\(a_i\bmod pb_i\), with

\[
 p\nmid b_i,\qquad b_i>1,\qquad
 \xi_i=a_i\bmod p\in\{2,\ldots,p-1\}.
 \tag{SA5}
\]

The \(b_i\) are pairwise distinct, because the corresponding
\(pb_i\) are distinct. For any fixed \(\xi\in\{2,\ldots,p-1\}\),
the list \(\mathcal S\), together with the cofactor classes
\(a_i\bmod b_i\) for which \(\xi_i=\xi\), covers the entire
\(p\)-free carrier. Prescribe that carrier point and first root
\(\xi\), and apply the current whole coverage to the same point.

Choose a fresh odd prime \(\ell\) dividing no current modulus.
Keep \(\mathcal S\) unchanged and add:

\[
 \begin{array}{ll}
 \text{pure powers:}&
     p^h\bmod p^{h+1},\quad 0\le h\le\ell-2;\\[1mm]
 \text{transported classes:}&
     x\equiv\xi_i p^h\pmod{p^{h+1}},\quad
     x\equiv a_i\pmod{b_i},
     \quad 0\le h\le\ell-2;\\[1mm]
 \text{closing classes:}&
     x\equiv0\pmod{p^j},\quad x\equiv j\pmod\ell,
     \quad 0\le j\le\ell-1.
 \end{array}
 \tag{SA6}
\]

Each displayed pair defines one CRT class. At \(j=0\), the
modulus-one condition is vacuous, and the closing class is
\(0\bmod\ell\).

If \(p^{\ell-1}\nmid x\), put \(h=v_p(x)\le\ell-2\).
First nonzero \(p\)-digit 1 is covered by the pure-power class.
For first nonzero digit \(\xi\ge2\), use the cofactor cover in
SA5: it supplies either a retained class of \(\mathcal S\) or
the corresponding transported class. If \(p^{\ell-1}\mid x\),
take \(j\in\{0,\ldots,\ell-1\}\) representing \(x\bmod\ell\).
Then \(p^j\mid x\), so its closing class covers \(x\). This
includes zero. A common period is
\(p^{\ell-1}\ell L\), where \(L\) is the lcm of the moduli in
\(\mathcal S\) and the \(b_i\), with empty lcm equal to one.

The new modulus types are \(p^{h+1}\), \(p^{h+1}b_i\), and
\(p^j\ell\). Freshness separates the last type from the first
two and from retained moduli. The condition \(b_i>1\) separates
transported classes from pure powers; \(p\nmid b_i\) and
distinctness of the \(b_i\) make \((h,b_i)\) recoverable from
the transported modulus. Positive \(p\)-height separates these
classes from retained \(p\)-free moduli. The only new \(p\)-free
modulus is the fresh prime \(\ell\).

Consequently the output repetitions are exactly the old repetitions
in \(\mathcal S\), with both original APs literally unchanged.
For any untreated original prime \(q\ne p,\ell\), transported
classes preserve their full \(q\)-adic exponent and residue, while
pure powers and closing classes introduce no \(q\) factor. In
particular, flatness at such a \(q\) is preserved.

The published
[Harrington--Sun--Wong, Theorem 3.2](../../../../../Library/Arith/harrington2021oddcovering.md)
assumes square-free input and only the prime repetition. The
\(p\)-flat extension was proved separately in
[348, section 2](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
The argument here checks the same construction with an arbitrary
retained \(p\)-free list; it does not attribute these broader
hypotheses to the published theorem.

## 3. Simultaneous absorption removes exactly the selected repetitions

Starting from \(\mathcal C^*\), apply section 2 successively at
each \(p\in P\). At every step choose the auxiliary prime outside
the entire initial prime support, \(P\), and every previously
introduced auxiliary prime. Only finitely many primes are forbidden.

At an untreated \(q\in P\), its two pure classes are retained,
its flatness is preserved, and it has no other repeated \(q\)-bearing
modulus. Thus the next step satisfies all the hypotheses of section 2.
After finitely many steps, the output is a whole cover whose repeated
numerical moduli are exactly

\[
 \{r\in\mathcal R:\gcd(r,\prod_{p\in P}p)=1\},
 \tag{SA7}
\]

with both APs at every such modulus literally unchanged.

If every input modulus is coprime to 6 and every selected prime in
\(P\) is at least 5, choose every auxiliary prime at least 5.
All output moduli remain nonunit and coprime to 6. Hence
SA3--SA4 are impossible when every original repeated modulus touches
\(P\): otherwise SA7 is empty, giving a distinct whole cover
forbidden by
[Hough--Nielsen, Theorem 1](https://arxiv.org/pdf/1703.02133v2).

This includes the repeated-prime-union pruning of report 381, by
taking \(P=\mathcal R\) when every repeated modulus is prime and
letting \(R_p\) be its actual repeated pair. It also permits one
prime's cylinders to absorb another prime's high classes. Testing
each prime's high roots against its own pair alone is a sufficient
but stronger requirement.

For example, take the partial data
\(R_7=R_{11}=\{0,1\}\) and the classes
\(44\bmod 7^2 11\), \(35\bmod 7\,11^2\).
Their respective high-prime first roots are 2 and 2, outside their
own pairs. But the first lies in root 0 at 11, and the second in
root 0 at 7. Both are contained in the joint union. These data
illustrate the difference between the tests; they are not a whole
cover or a counterexample to an odd-cover conjecture.

## 4. Distinct prime representatives force an exposed square

Continue with a whole cover whose moduli are coprime to 6. For
\(r\in\mathcal R\), write
\(\operatorname{supp}(r)=\{p:p\mid r\}\). A system of distinct
representatives is an injective map

\[
 r\longmapsto p_r\in\operatorname{supp}(r).
 \tag{SA8}
\]

Fix any such map. Put \(P=\{p_r:r\in\mathcal R\}\), and for each
assigned pair choose \(R_{p_r}\) of size two containing \(U_{p_r}\)
and at least one first-\(p_r\) root of that pair. These choices
always exist. If a pure prime \(p\) repeats, its label \(r=p\)
has only representative \(p\), and \(R_p\) is its actual pair.
If \(p\) is assigned to a composite label, injectivity excludes a
repeated pure-prime label \(p\), so \(|U_p|\le1\); add one
endpoint of the assigned pair, and fill to two roots if needed.

SA4 holds, and every repeated modulus touches \(P\). Section 3
therefore forces an original class satisfying

\[
 \begin{gathered}
 A=(a\bmod m)\in\mathcal C,\qquad
 p^2\mid m\text{ for some }p\in P,\qquad A\not\subseteq V,\\
 \text{equivalently}\qquad
 a\bmod q\notin R_q\quad\text{for every }q\in P\text{ dividing }m.
 \end{gathered}
 \tag{SA9}
\]

Thus either no SDR exists, or SA9 holds for **every** SDR and
**every** compatible root-pair assignment. The witness is an
original class, because SA3 was tested before the auxiliary
enlargement or any surgery. It has a point outside the whole union;
it need not be disjoint from the union at selected primes not
dividing its modulus. One class can witness several primes or
several assignments, so its mass cannot be counted independently
for each occurrence.

There is also an incidence-only consequence. Let

\[
 F=\{p:\text{no original input modulus is divisible by }p^2\}.
\]

There can be no SDR with \(p_r\in\operatorname{supp}(r)\cap F\),
since SA9 would have no square-bearing witness. By finite Hall's
theorem, some nonempty \(\mathcal R'\subseteq\mathcal R\) satisfies

\[
 |\mathcal R'|>
 \left|\bigcup_{r\in\mathcal R'}
       (\operatorname{supp}(r)\cap F)\right|.
 \tag{SA10}
\]

Only the assigned primes need to be flat; heights at all other
primes are unrestricted. If every prime dividing a repeated modulus
belongs to \(F\), the intersections with \(F\) can be omitted.
In that case all repeated moduli are square-free, and there are at
least three of them: one nonunit support has at least one prime,
and two distinct nonempty square-free supports have union of size
at least two, so neither a one-label nor a two-label set can violate
Hall.

If, in addition, all repeated moduli are products of exactly two
distinct primes, form the simple graph with primes as vertices and
repeated moduli as edges. SA10 gives an edge set with more edges
than incident vertices. Some connected component therefore has
\(e>v\), so its cycle rank \(e-v+1\) is at least two. Such a
simple component requires at least four vertices and five edges.
This is a necessary condition under the stated flatness premise,
not a sufficient covering criterion.

## 5. Lift the alternative to the actual missing-5 fibre

Use the hypothetical extremal family of
[350, EB1--EB3](../321-384/350-extremal-paired-branch-and-source-support.md)
and the saturated missing first-5 fibre \(F_v\) of
[380, HB5--HB7](380-small-prime-survivors-and-original-haar-costs.md).
Original prime classes are normalized to \(0\bmod p\). The active
originals satisfy

\[
 3\nmid d,\qquad
 5\nmid d\ \text{or}\ a_d\equiv v\pmod5,
 \qquad m(d)=d/5^{\mathbf1_{5\mid d}}.
 \tag{SA11}
\]

They give a whole quotient cover with numerical multiplicity at most
two and moduli coprime to 6. Its repeated numerical moduli \(r\)
come from original pairs \(r,5r\), with \((r,30)=1\). The two
quotient residues differ. For any \(p\mid r\), \(p\ne5\), and
the parametrization \(x=v+5z\) applies the same invertible affine
map to every class's root modulo \(p\). Thus SA2 and SA9 can be
tested in original coordinates, and division by 5 does not change
any selected prime's exponent.

For an SDR of the repeated bases, one may always choose, in original
coordinates,

\[
 R_{p_r}=\{0,u_r\},\qquad u_r\ne0.
 \tag{SA12}
\]

If \(r=p_r\), take \(u_r=a_{5p_r}\bmod p_r\). If \(r\) is
composite, take either endpoint
\(a_r\bmod p_r\) or \(a_{5r}\bmod p_r\); both are nonzero
by comparable-original disjointness. The pure original \(p_r\)
is active. An additional active original \(5p_r\) would make
\(p_r\) a repeated base and reserve its representative, so it
cannot occur when \(p_r\) is assigned to a composite base.

For every such SDR and endpoint choice, SA9 supplies an original
label \(d\) with

\[
 \begin{gathered}
 3\nmid d,\qquad
 5\nmid d\ \text{or}\ a_d\equiv v\pmod5,\qquad
 p^2\mid d\text{ for some selected }p,\\
 a_d\bmod q\notin\{0,u_{r(q)}\}
       \quad\text{for every selected }q\mid d.
 \end{gathered}
 \tag{SA13}
\]

Here \(r(q)\) is the unique repeated base assigned to \(q\).
The activity condition is retained; this is not merely a statement
that the full original period has a high prime exponent.

In particular, suppose the quotient has exactly one repeated modulus,
a composite \(r\). For every \(p\mid r\) and every
\(u\in\{a_r\bmod p,a_{5r}\bmod p\}\), there is an active
original \(d\) with

\[
 p^2\mid d,\qquad a_d\bmod p\notin\{0,u\}.
 \tag{SA14}
\]

If \(r\) is square-free, this witness lies outside the pair
\(r,5r\). If \(p^2\mid r\), a member of the pair itself may
supply it. Different primes and endpoints need not give different
original labels.

## 6. Exact finite controls for the surgery

The whole even cover
\(0\bmod2,\ 1\bmod3,\ 3\bmod6,\ 5\bmod6\) has period 6 and
only modulus 6 repeated. Take \(p=3\), \(R_3=\{0,1\}\), and
\(\ell=5\). Absorption deletes \(1\bmod3\) and \(3\bmod6\)
before inserting the two pure-3 classes. The retained class is
\(0\bmod2\), and the surviving transported cofactor is
\(1\bmod2\) at root 2.

SA6 produces the following residue/modulus pairs:

\[
 \begin{gathered}
 (0,2),\\
 (1,3),(3,9),(9,27),(27,81),\\
 (5,6),(15,18),(45,54),(135,162),\\
 (0,5),(6,15),(27,45),(108,135),(324,405).
 \end{gathered}
 \tag{SA15}
\]

Exact integer enumeration over all 810 residues of the full output
period found zero uncovered residues and 14 distinct moduli. Replacing
the input \(0\bmod2\) by \(0\bmod4,2\bmod4\) instead gives 15
output classes covering every one of the 1620 residues of its full
period. Its only repeated modulus is 4, with both original residues
0 and 2 unchanged. These controls include zero, the maximal closing
index, and preservation of a repeated \(p\)-free modulus. Both
inputs are even covers, not coprime-to-6 or odd-cover counterexamples.

## 7. Hall deficiency does not itself give a uniform original cost

There are actual partial families satisfying the local original
conditions and exhibiting Hall deficiency while their mixed-modulus
cost becomes arbitrarily small relative to their no-prime mass.
Choose primes \(7\le p<q<2p\), and include every odd prime label
at most \(q\), with residue zero. Add original labels
\(5p,5q,pq,5pq\). Set the first two residues to 1, the third to 3,
and define the last by

\[
 a_{5pq}\equiv1\pmod5,\qquad
 a_{5pq}\equiv2\pmod p,\qquad
 a_{5pq}\equiv2\pmod q.
 \tag{SA16}
\]

The palette is divisor-closed above one. Every comparable pair of
classes is disjoint: composites avoid prime root zero; the top
\(5pq\) class differs from \(5p\) and \(5q\) at roots \(p,q\),
and from \(pq\) at both. The family is irredundant. A pure-prime
class has a private point with its own coordinate zero and every
other prime coordinate 4. Private points for the four composites,
listed as \((x\bmod5,x\bmod p,x\bmod q)\), are

\[
 (1,1,4),\quad(1,4,1),\quad(2,3,3),\quad(1,2,2),
 \tag{SA17}
\]

with every other prime coordinate set to 2.

Restrict its 3-free part to the literal first-5 root 1 and remove that
one 5 factor. The repeated bases are exactly \(p,q,pq\), so three
labels have only two prime representatives. All moduli are square-free.
Nevertheless the reciprocal sum of its four original mixed moduli is

\[
 W_{\mathrm{mix}}=\frac1{5p}+\frac1{5q}+\frac6{5pq}.
 \tag{SA18}
\]

The original weighted mixed cost of
[361, PR5](../321-384/361-prime-overlap-reservation-for-composite-parents.md)
satisfies \(0\le M_{\mathrm{comp}}\le W_{\mathrm{mix}}\), since
every coefficient \(c_d\) lies in \([0,1]\). The pure-survivor mass
is \(X=P_0\) here, because there are no higher pure-power labels.
For \(P_0=\prod_{3\le s\le q,\ s\text{ prime}}(1-1/s)\), the
elementary bound \(P_0\ge q^{-1/2}\) used in
[381, section 6](381-repeated-prime-exposure-in-missing-fibres.md)
gives

\[
 \frac{M_{\mathrm{comp}}}{X}\le
 \frac{W_{\mathrm{mix}}}{P_0}\le W_{\mathrm{mix}}\sqrt q
 \le\left(\frac2{5p}+\frac6{5p^2}\right)\sqrt{2p}
 \longrightarrow0.
 \tag{SA19}
\]

Bertrand's postulate provides such \(q\) for arbitrarily large prime
\(p\). These are partial families: for each nonzero first-5 root,
set the \(p,q\) roots to 4 and all other prime roots to 2. The
resulting point is uncovered. Thus the actual residual has all four
nonzero first-5 roots; the saturation hypothesis of section 5 fails.
This example refutes a uniform-cost consequence from the listed local
conditions and Hall deficiency alone, not from whole coverage.

The remaining proof obligation is to combine whole-fibre coverage,
the Hall obstruction or exposed-square alternative, and a quantitative
bound on one common original family. The auxiliary construction supplies
no measure-preserving map that would allow its new classes or increased
heights to be charged directly to the original Haar budget.
