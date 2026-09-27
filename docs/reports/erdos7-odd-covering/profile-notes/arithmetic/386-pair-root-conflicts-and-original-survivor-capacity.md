[Index](../../marked_head_profile.md) · [Simultaneous absorption](383-simultaneous-root-absorption-and-hall-obstructions.md) · [Original missing-fibre quotient](380-small-prime-survivors-and-original-haar-costs.md)

# Pair-root conflicts and original survivor capacity

A finite congruence family with moduli coprime to 6 and numerical
multiplicity at most two can be tested by choosing at most two forbidden
first-root patterns for each pair of support primes. Classes captured
by those patterns are avoided together. The remaining mixed classes
can be avoided by assigning each to one support prime and paying for
its full prime-power prefix there. High exponents lower this assigned
cost. Pure-prime-power classes have a separate summable cost, so no
square-free or bounded-height assumption is required.

For the literal missing-5 quotient of report 380, a partial assignment
also constructs a positive-mass set inside the original no-prime
region. Only unmatched original labels can cover that set, and their
capacities are their exact intersections in the same original Haar
probability. The remaining 5-adic digits are included when the quotient
still has a factor of 5.

These are repository-derived finite mathematical deductions from sequential coordinate
selection, capacitated Hall matching, a pure-power tail estimate, and
CRT. The weighted assignment is indivisible; its feasibility is not
identified with ordinary Hall matching. The results do
not establish that every hypothetical saturated quotient passes the
test, supply a uniform improvement to the original budget, or resolve
unrestricted Erdős #7. No literature-novelty or Lean-verification claim
is made.

## 1. Capture classes by pair-root tables

Let

\[
 \mathcal C=\{C_d=b_d\bmod m_d:d\in D_*\}
 \tag{PC1}
\]

be a finite indexed family with \(m_d>1\), \(\gcd(m_d,6)=1\), and
at most two labels at each numerical modulus. The label \(d\) is kept
separate from \(m_d\). In the original-fibre application it is the
original numerical modulus. All counts below count labels; no
identification of original labels or change of their costs is made.

List the distinct support primes and their actual maximum heights:

\[
 p_1<\cdots<p_n,\qquad H_i=\max_{d\in D_*}v_{p_i}(m_d).
\]

Write \(\mathbb F_p=\mathbb Z/p\mathbb Z\), and let

\[
 U_i=\{b_d\bmod p_i:m_d=p_i\},\qquad u_i=|U_i|\le2.
 \tag{PC2}
\]

For each \(i<j\), choose a table

\[
 T_{ij}\subseteq\mathbb F_{p_i}\times\mathbb F_{p_j},
 \qquad |T_{ij}|\le2.
 \tag{PC3}
\]

A class with at least two support primes is **captured** if, for some
\(i<j\) with \(p_ip_j\mid m_d\),

\[
 (b_d\bmod p_i,b_d\bmod p_j)\in T_{ij}.
 \tag{PC4}
\]

The class is then contained in the corresponding pair-root cylinder.
Its higher digits and original label are retained. Let \(E\subseteq D_*\)
be the labels of mixed-support classes that are not captured.

For \(j<i\), define the residue-sensitive conflict count

\[
 \begin{aligned}
 \beta_{ji}
 &=\max_{s\in\mathbb F_{p_j}\setminus U_j}
   \bigl|\{t\in\mathbb F_{p_i}\setminus U_i:(s,t)\in T_{ji}\}\bigr|,\\
 s_i&=\sum_{j<i}\beta_{ji},\\
 k_i&=p_i-u_i-s_i-1.
 \end{aligned}
 \tag{PC5}
\]

The maximum is over a nonempty set, since \(p_j\ge5\) and
\(u_j\le2\). Each \(\beta_{ji}\le2\). Distinct odd primes at least
5 satisfy \(p_i\ge2i+3\), so

\[
 k_i\ge(2i+3)-2-2(i-1)-1=2.
 \tag{PC6}
\]

## 2. A weighted assignment uses the full exponent heights

For each prime, measure a forbidden prefix in units of one first-root
fibre. The actual higher pure-power load is

\[
 \lambda_i=
 \sum_{\substack{d\in D_*:\ m_d=p_i^a\text{ for some }a\ge2}}
       p_i^{1-a}.
 \tag{PC7}
\]

The exponent \(a\) in each summand is determined by \(m_d\).
Numerical multiplicity at most two gives

\[
 \lambda_i\le 2\sum_{a=2}^{H_i}p_i^{1-a}
 <\frac2{p_i-1}\le\frac12.
 \tag{PC8}
\]

Choose \(J\subseteq E\), and assign each label in \(J\) to one
dividing prime:

\[
 f:J\longrightarrow\{1,\ldots,n\},\qquad p_{f(d)}\mid m_d.
\]

Let

\[
 \begin{aligned}
 w_i&=\sum_{\substack{d\in J:\ f(d)=i}}
              p_i^{1-v_{p_i}(m_d)},\\
 \rho_i&=1-\frac{u_i+s_i+\lambda_i+w_i}{p_i}.
 \end{aligned}
 \tag{PC9}
\]

**Weighted survivor criterion.** If every \(\rho_i>0\), there is a
set \(\widetilde W\) in the quotient CRT carrier avoiding all
captured classes, all labels in \(J\), and all pure-power classes,
with uniform quotient mass

\[
 \nu(\widetilde W)\ge\prod_i\rho_i>0.
 \tag{PC10}
\]

In particular, if \(J=E\), the input family does not cover.

For the proof, choose the **full** coordinate modulo \(p_i^{H_i}\)
in increasing prime order. For any legal choices at earlier primes,
the roots in \(U_i\) and conflicts with their first roots exclude at
most \((u_i+s_i)p_i^{H_i-1}\) full coordinate values. The pure-power
classes of exponent at least two exclude at most
\(\lambda_i p_i^{H_i-1}\) values. Avoiding each assigned class at
this coordinate means avoiding its actual congruence modulo
\(p_i^{v_{p_i}(m_d)}\), so these prefixes exclude at most
\(w_i p_i^{H_i-1}\) further values. Overlap only decreases the
number excluded. At least

\[
 p_i^{H_i-1}(p_i-u_i-s_i-\lambda_i-w_i)
 =p_i^{H_i}\rho_i
 \tag{PC11}
\]

choices remain for **every** legal preceding coordinate tuple.
Multiplying these uniform lower bounds on successive numbers of
extensions proves PC10. This is a count on the same finite product
carrier, not an independence assertion after conditioning.

Each captured class fails a pair constraint; each assigned class fails
its designated full prefix; all pure-power classes were explicitly
excluded. CRT supplies the corresponding actual integers. A label is
assigned to one prime, not split fractionally among several primes.
No weighted version of the Hall equivalence is asserted.

## 3. Capacitated Hall is a simpler sufficient condition

The count condition

\[
 |f^{-1}(i)|\le k_i
 \tag{PC12}
\]

implies \(w_i\le k_i\), because every assigned prefix cost is at
most one. Together with \(\lambda_i<1/2\) and PC5, this gives
\(\rho_i\ge(1-\lambda_i)/p_i>0\). Thus the weighted criterion
contains the count-based certificate.

For assignment of all exceptional labels, finite Hall matching says
that PC12 is equivalent to

\[
 |D'|\le
 \sum_{\substack{i:\exists d\in D',\ p_i\mid m_d}}k_i
 \qquad(D'\subseteq E).
 \tag{PC13}
\]

Indeed, replace each prime vertex by \(k_i\) copies. Consequently a
hypothetical whole cover forces, for **every** choice of tables, a
nonempty exceptional subset violating PC13. Failure of PC13 does not
rule out an indivisible weighted assignment satisfying PC9.

Two consequences are useful:

* If every mixed class is captured, no assignment is needed. In
  particular, this holds when every mixed support has exactly two
  primes and each support pair uses at most two distinct first-root
  patterns, regardless of its finite exponent heights.
* At most four exceptional mixed classes always admit an assignment.
  Every nonempty subset involves at least two primes, whose combined
  capacity is at least four by PC6. Thus PC13 holds for every subset.

An exact fixed-table control consists of the four pure classes
\(0,1\bmod5\), \(0,1\bmod7\), and the eighteen mixed classes

\[
 r\bmod5^a7^b,\qquad 1\le a,b\le3,\quad r\in\{2,3\}.
\]

This general quotient input has numerical multiplicity two; it is not
asserted to be a distinct original family. Take empty tables. The count
capacities are \(k_5=2\), \(k_7=4\), so eighteen exceptional labels
violate PC13. Assign the residue2 class at \((a,b)=(1,1)\), all six
classes with \(a=3\), and the two classes with \((a,b)=(2,1)\) to5;
assign the remaining nine classes to7. Then

\[
 w_5=\frac{41}{25}<2,\qquad w_7=\frac{81}{49}<4,\qquad
 \rho_5=\frac{34}{125},\qquad\rho_7=\frac{164}{343},
\]

with \(\lambda_5=\lambda_7=0\). There are 45 surviving full5
coordinates and 189 surviving full7 coordinates. Thus the constructed
set has 8505 residues in period42875, all outside the 22 input classes,
while PC11 guarantees at least \(34\cdot164=5576\) residues. Direct
enumeration agrees. This distinguishes the two tests for fixed empty
tables only; it claims neither an improvement over every table choice
nor an exclusion beyond the ordinary union bound for this small input.

For context, assigning a clause to one of its variables with a bounded
number of available domain values is the mixed-domain matching
framework of [Kullmann, Lemma 1.7.1](../../../../../Library/Combinatorics/kullmann2011clausal.md).
A selected pair-root pattern is exactly an ordered colour conflict in
the model of [Dvořák--Esperet--Kang--Ozeki](../../../../../Library/Combinatorics/dvorak2020singleconflict.md);
multiple patterns correspond to parallel conflict edges. The proof
above uses its unequal prime-sized domains directly and imports no
quantitative colouring threshold.

## 4. Exact capacities on the same weighted survivor

Fix the tables and an assignment of \(J\subseteq E\) with positive
\(\rho_i\). Let \(L=E\setminus J\), and write

\[
 G=\{(t_i)_i:t_i\notin U_i,
          \ (t_i,t_j)\notin T_{ij}\text{ for every }i<j\}.
 \tag{PC14}
\]

For \(t\notin U_i\), define the actual higher-digit survivor and its
ambient coordinate mass by

\[
 \begin{aligned}
 V_i(t)=\{y\bmod p_i^{H_i}:\;&y\equiv t\pmod{p_i},\\
   &y\text{ avoids every input class of modulus }p_i^a,\\
   &y\not\equiv b_d\pmod{p_i^{v_{p_i}(m_d)}}
                       \text{ for every }d\in J\text{ with }f(d)=i\},\\
 \alpha_i(t)&=\frac{|V_i(t)|}{p_i^{H_i}}.
 \end{aligned}
 \tag{PC15}
\]

Some individual \(V_i(t)\) may be empty. The actual jointly surviving
set is the disjoint union

\[
 \widetilde W=\coprod_{t\in G}\prod_i V_i(t_i).
 \tag{PC16}
\]

By exact CRT counting and the successive-extension estimate PC11,

\[
 \nu(\widetilde W)
 =\sum_{t\in G}\prod_i\alpha_i(t_i)
 \ge\prod_i\rho_i>0.
 \tag{PC17}
\]

Every captured class, matched class, and pure-power class misses
\(\widetilde W\). Only labels in \(L\) can cover it.

For \(d\in L\), let \(e_{i,d}=v_{p_i}(m_d)\) and set

\[
 \alpha_{i,d}(t)=
 \frac{|\{y\in V_i(t):y\equiv b_d\pmod{p_i^{e_{i,d}}}\}|}
      {p_i^{H_i}},
 \tag{PC18}
\]

where the extra congruence imposes no restriction when \(e_{i,d}=0\).
Then the exact capacity of that labelled class on the constructed
survivor is

\[
 \nu(\widetilde W\cap C_d)
 =\sum_{t\in G}\prod_i\alpha_{i,d}(t_i).
 \tag{PC19}
\]

These are finite counts using the actual residues. Neither independence
after conditioning on mixed classes nor substitution of a new witness
law is asserted.

## 5. Lift the capacity to the same original Haar probability

Use the original family and normalization of
[380, section 1](380-small-prime-survivors-and-original-haar-costs.md):
distinct odd moduli \(d>1\), a divisor-closed palette, comparable
original classes disjoint, and \(A_p=0\bmod p\) for every support
prime. Assume explicitly that \(3,5\in D\). Write

\[
 Q=\mathop{\rm lcm}D,\qquad B=Q/3^{H_3},\qquad
 P_0=\prod_{p\mid Q}(1-1/p),
 \tag{PC20}
\]

and let \(\mathsf H\) be uniform probability modulo \(Q\). Assume
the literal nonzero first-5 fibre

\[
 F_v=\{x\bmod B:x\equiv v\pmod5\},\qquad v\ne0,
 \tag{PC21}
\]

is entirely covered by original 3-free classes, as in the saturated
branch of report 380. Parametrize it by
\(\theta(z)=v+5z\), \(z\bmod B/5\). The active original labels are

\[
 D_*=
 \{d\in D:3\nmid d,\quad5\nmid d\text{ or }a_d\equiv v\pmod5\}.
 \tag{PC22}
\]

Their pullbacks have the actual quotient residues \(b_d\) and moduli

\[
 m_d=d/5^{\mathbf1_{5\mid d}}.
 \tag{PC23}
\]

They meet PC1: modulus one is absent because the original prime-5
class misses \(F_v\); all moduli are coprime to 6; positive output
5-exponent has at most one source, while zero output 5-exponent has
at most the two sources \(r,5r\).

Apply the weighted criterion and PC14--PC19 to this quotient. Any
coordinates of \(B/5\) not used by its classes remain free. In particular, when a quotient class
still has a factor of 5, **5 remains a quotient support prime** and
its coordinate in PC15 counts the remaining original 5-adic digits.
At primes other than 5, quotient roots are obtained by one invertible
affine change of coordinates. At 5, the quotient first digit is the
next original digit after the fixed root \(v\).

Lift \(\widetilde W\) through \(\theta\) and allow exactly the
original 3-coordinate values with first root nonzero. Call the resulting
subset of \(\mathbb Z/Q\mathbb Z\) \(W\). It lies in the original
no-prime set

\[
 Z=\{x:x\not\equiv0\pmod p\text{ for every }p\mid Q\}.
\]

For \(p\ne3,5\), the active original prime class has its quotient
root in \(U_i\), so PC14 excludes it. The roots at 3 and 5 are excluded
by the explicit lift conditions. Direct CRT counting in the original
space gives

\[
 \begin{aligned}
 \mathsf H(W)
 &=\frac2{15}\sum_{t\in G}\prod_i\alpha_i(t_i)\\
 &\ge\frac2{15}\prod_i\rho_i>0,\\
 \kappa_d:=\mathsf H(W\cap A_d)
 &=\frac2{15}\sum_{t\in G}\prod_i\alpha_{i,d}(t_i)
 \qquad(d\in L).
 \end{aligned}
 \tag{PC24}
\]

Here \(2/15=(2/3)(1/5)\) charges the original nonzero first-3 root
and fixed first-5 root. It does not remove the residual quotient-5
factor. Unused higher digits remain free, so PC24 also applies when
the active quotient has smaller heights than the original period.

The asserted whole coverage of \(F_v\) forces

\[
 W\subseteq\bigcup_{d\in L}A_d,
 \qquad
 \sum_{d\in L}\kappa_d\ge\mathsf H(W).
 \tag{PC25}
\]

For an ordering of \(L\), the sets

\[
 W_d=(W\cap A_d)\setminus\bigcup_{e<d}A_e
\]

partition \(W\) under PC25 and satisfy \(\mathsf H(W_d)\le\kappa_d\).
They allocate mass once per original label; they need not be private
regions of an irredundant cover.

Every label in \(L\) is an original composite, and comparable-original
disjointness makes its residue nonzero at every prime dividing it.
Therefore its old no-prime capacity is exactly

\[
 \kappa_d\le\mathsf H(A_d\cap Z)
 =\frac{P_0}{\varphi(d)}.
 \tag{PC26}
\]

PC24 refines this capacity on a constructed literal subset. Finding
tables and a partial assignment for which
\(\sum_{d\in L}\kappa_d<\mathsf H(W)\) contradicts the saturated
branch. No support-uniform positive lower bound on the product in PC24,
or sufficient upper bound on all remaining \(\kappa_d\), is established here.

## 6. Exact control with a residual quotient-5 coordinate

Take the original residue/modulus pairs

\[
 (0,3),\ (0,5),\ (0,7),\ (1,25),\ (16,35),\ (4,49),\ (11,175).
 \tag{PC27}
\]

This is a partial family. The original period is \(3675=3\cdot25\cdot49\).
On the literal first-5 root 1, the quotient has pure first-root sets
\(U_5=\{0\}\), \(U_7=\{3,4\}\), the pure49 residue 30, and the
mixed35 residue 2 from the original label 175.

Choose empty pair tables and match no mixed label. The set \(W\)
requires

\[
 x\not\equiv0\pmod3,\quad x\equiv1\pmod5,\quad
 x\not\equiv1\pmod{25},\quad x\not\equiv0\pmod7,\quad
 x\not\equiv16\pmod{35},\quad x\not\equiv4\pmod{49}.
\]

There are four allowed residual roots at 5. At 7, five first roots
remain, giving 35 lifts modulo49, of which the pure49 class deletes one.
For the unmatched original label175, the residual5 root is fixed and
six of the seven lifts at its first7 root survive. Thus

\[
 \begin{aligned}
 |W|&=272,&
 \mathsf H(W)&=\frac2{15}\frac45\frac{34}{49}
                 =\frac{272}{3675},\\
 |W\cap A_{175}|&=12,&
 \kappa_{175}&=\frac2{15}\frac15\frac6{49}
                 =\frac4{1225}.
 \end{aligned}
 \tag{PC28}
\]

Direct integer enumeration over all 3675 residues agrees with these
counts. In particular, the original first-5 factor and the residual
quotient-5 factor both occur.

## 7. Comparison with block absorption and scalar budgets

For a finite set \(P\) of primes at least 7, include original classes
\(0\bmod\ell\) for \(\ell\in\{3,5\}\cup P\), together with

\[
 \begin{gathered}
 1\bmod5p,\qquad4\bmod p^2\qquad(p\in P),\\
 3\bmod pq\qquad(p<q\text{ in }P),\\
 A_{5pq}:\quad x\equiv1\pmod5,\quad
 x\equiv2\pmod p,\quad x\equiv2\pmod q.
 \end{gathered}
 \tag{PC29}
\]

The numerical palette is distinct and divisor-closed above one, and
comparable original classes are disjoint. On first-5 root 1, each
\(p\) repeats at roots 0,1, while each \(pq\) repeats at root pairs
\((3,3),(2,2)\). Coordinates here are original first roots; the common
affine map gives the corresponding quotient coordinates.

Every block choice hitting all repeated pure primes must select each
\(p\) with its actual pair \(\{0,1\}\). Its square class at root4
then lies outside the entire selected union, so the absorption test in
383 fails. In contrast, tables consisting of the affine images of
\((2,2),(3,3)\) in quotient coordinates capture every mixed quotient
class. There are no exceptional labels, so the certificate proves
noncoverage. A direct CRT hole has root1 at3 and5 and root5 at every
\(p\in P\).

The scalar quantities for this family are

\[
 \begin{aligned}
 R_{\rm quotient}
 &=\sum_{p\in P}\left(\frac2p+\frac1{p^2}\right)
     +\sum_{p<q\text{ in }P}\frac2{pq},\\
 S_0
 &=\sum_{p\in P}\left(\frac1{4(p-1)}+\frac1{p(p-1)}\right)
     +\sum_{p<q\text{ in }P}\frac5{4(p-1)(q-1)}.
 \end{aligned}
 \tag{PC30}
\]

For \(P=\{7,11,13,17\}\), exact arithmetic gives

\[
 R_{\rm quotient}=\frac{253544736}{289578289}<1,
 \qquad S_0=\frac{8706619}{39207168}<1.
 \tag{PC31}
\]

That small control is already excluded by both scalar union bounds;
it supplies no additional exclusion beyond them.

For \(P\) equal to all 71 primes from 7 through 373, PC29 has 5185
original labels. Exact rational comparisons give

\[
 \frac{501}{500}<S_0<\frac{401}{400},
 \qquad
 \frac{153}{50}<R_{\rm quotient}<\frac{307}{100}.
 \tag{PC32}
\]

Both scalar exclusion tests now fail, while the pair certificate works
and block absorption still fails. This establishes a distinction from
those two scalar tests only. These partial families contain no mixed
original modulus divisible by3. If one covered, fixing a nonzero3 root
would already give a distinct whole cover with moduli coprime to6,
contradicting [Hough--Nielsen, Theorem 1](https://arxiv.org/pdf/1703.02133v2).
Thus PC32 does not establish an exclusion beyond every existing method,
nor does it realize the actual saturated branch.

The remaining whole-cover obligation is to produce useful pair tables
and assignments for the actual original residues, or to bound the exact
unmatched capacities in PC25. A Hall deficit by itself does not supply
the missing original-Haar charge.

The [exact control program](../../frontier/cover-geometry/pair_root_capacity_controls.py)
and its [rational counts and input data](../../frontier/cover-geometry/pair_root_capacity_controls.json)
reproduce PC28, PC31, PC32 and the full-height fixed-table comparison.
The finite controls check these examples; PC10 and PC24 hold at arbitrary
finite support sizes and heights by the proofs above.
