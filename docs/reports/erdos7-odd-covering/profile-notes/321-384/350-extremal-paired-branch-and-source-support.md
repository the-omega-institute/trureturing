[Index](../../marked_head_profile.md) · [Original overlap](347-original-overlap-leakage-gives-a-uniform-reciprocal-gap.md) · [Jenkin--Simpson source](../../../../../Library/Arith/jenkin2003compositecovering.md)

# Extremal odd-cover branches and the support of private and overlap witnesses

Conditional on a distinct odd covering system existing, one may choose an extremal system whose modulus set is closed under taking divisors greater than one. Every non-prime-class branch then has at least one paired residual modulus, each pair coming from original moduli \(m,pm\). Original private points force a covering selection to retain every child side of these pairs, while minimum cardinality forces that all-child selection to fail.

The resulting two sets of holes have different source meanings. One avoids all earlier classes and has positive mass under the pre-stage Haar survivor law. The earlier-ending part of the other is already covered by earlier classes, so every pre-stage killed law assigns it mass zero. This support distinction prevents a proposed direct comparison with report 347's positive original-Haar overlap mass.

These are ordinary finite deductions using standard covering-system reductions. They do not establish a distinct odd cover, its nonexistence, a new literature theorem, or new Lean content.

## 1. Extremality supplies the divisor structure

Assume there is a finite cover \(\mathcal C\) of all integers by classes \(A_d=a_d\bmod d\), with distinct odd \(d>1\). Among all such covers, choose \(\mathcal C_*\) lexicographically minimizing

\[
\left(n,\sum_{d\in D}d\right),\qquad n=|D|.
\tag{EB1}
\]

The first minimum and then the second exist by well-ordering of the positive integers. Minimum cardinality implies irredundancy: every original class has an integer in no other original class.

If \(1<e\mid d\) and \(e\notin D\), replacing \(A_d\) by the containing class \(a_d\bmod e\) preserves coverage, oddness and modulus distinctness, keeps \(n\) fixed, and decreases the second coordinate of EB1. Thus

\[
d\in D,\quad 1<e\mid d\quad\Longrightarrow\quad e\in D.
\tag{EB2}
\]

This uses the divisor-replacement observation in Jenkin--Simpson, *Composite covering systems of minimum cardinality*, Integers 3 (2003), A13, [Lemma 1, PDF p. 3](../../../../../Library/Arith/jenkin2003compositecovering.md). Their composite-only canonical family permits composite divisors; the present admissible class permits every odd divisor greater than one. No prime relabeling is used here.

If \(e,d\in D\), \(e\mid d\), and \(e<d\), then \(A_e\cap A_d\) is empty. A nonempty intersection would give \(A_d\subseteq A_e\), contrary to irredundancy. In particular every support prime \(p\) occurs as an original modulus. One global CRT translation normalizes all of them to

\[
A_p=0\bmod p.
\tag{EB3}
\]

Every other original class whose modulus is divisible by \(p\) is then disjoint from the entire first-digit-zero branch at \(p\).

The prime support is an initial segment of the odd primes. Otherwise let \(r<q\) be an absent odd prime below a present prime \(q\), and write \(Q=q^H M\). Inject the \(r\)-digits into \(q\)-digits at every level, choosing the first-digit image to avoid the original class \(A_q\). Together with the identity on \(\mathbb Z/M\mathbb Z\), this defines an injection from the complete \(r^H M\) carrier into the original carrier.

Every original AP of modulus \(q^e m\) pulls back either to the empty set or to one AP of modulus \(r^e m\): each required prefix digit has at most one inverse. The modulus map is injective because \(r\) was absent. The pullbacks cover the whole new carrier, remain odd and nonunit, and omit \(A_q\), contradicting minimum cardinality.

This adapts the prime compression behind Jenkin--Simpson Lemma 2; their statement uses the initial ordinary primes starting at 2. The digit injection is not a Haar-preserving transport.

## 2. Exact branch restriction retains every higher digit

Write the full original period as \(Q=\prod_p p^{H_p}\), and fix a support prime \(p\). Use the common branch carrier

\[
\Omega_p=\mathbb Z/p^{H_p-1}\mathbb Z
             \times\prod_{q\ne p}\mathbb Z/q^{H_q}\mathbb Z.
\tag{EB4}
\]

For \(r\in\{0,\ldots,p-1\}\), define \(\iota_r:\Omega_p\to\mathbb Z/Q\mathbb Z\) by setting the \(p\)-coordinate to \(r+pu\), where \(u\) is the first coordinate of \(\Omega_p\), and keeping all other CRT coordinates. This is a bijection onto the first-\(p\)-digit branch \(r\). The base is also a cyclic group of order \(Q/p\); a literal restricted original class is a single AP on that group, with modulus

\[
d\quad(p\nmid d),\qquad d/p\quad(p\mid d, a_d\equiv r\pmod p).
\tag{EB5}
\]

Inactive \(p\)-bearing originals disappear. This is the branch reduction of Jenkin--Simpson, Theorem 8, PDF pp. 7--8, with residues and provenance retained. Their original definition permits a multiset of residual moduli. The reduction assumes neither squarefreeness nor height one.

Take \(r\ne0\). The prime class \(A_p\) is inactive, so no residual modulus is one. Two different originals can have the same residual modulus only if they are

\[
m,\ pm,\qquad p\nmid m,\quad m>1.
\tag{EB6}
\]

Within each of the \(p\)-free and \(p\)-bearing lists the map in EB5 is injective, so there are no triple collisions. Define

\[
E_{p,r}=\{m>1:p\nmid m,\ pm\in D,\ a_{pm}\equiv r\pmod p\}.
\tag{EB7}
\]

Every \(m\in E_{p,r}\) is an original modulus by EB2. Let \(P_m=\iota_r^{-1}(A_m)\) and \(C_m=\iota_r^{-1}(A_{pm})\). They are distinct disjoint APs of the same residual modulus \(m\). Let \(U_{p,r}\) be the union of all active residual classes whose modulus occurs only once. Then

\[
\Omega_p=U_{p,r}\cup\bigcup_{m\in E_{p,r}}P_m
                       \cup\bigcup_{m\in E_{p,r}}C_m.
\tag{EB8}
\]

The set \(E_{p,r}\) is nonempty. Otherwise EB8 itself would be a cover with distinct odd nonunit moduli and fewer than \(n\) classes, since at least \(A_p\) disappeared. This contradicts the first minimum in EB1. Thus every nonzero first \(p\)-digit has an actual exponent-one \(p\)-bearing original child. This existence statement does not say that these children cover the same cofactor states across branches.

## 3. Private points force the child side of every pair

Define two subsets of the same base:

\[
X_{p,r}=\Omega_p\setminus
       \left(U_{p,r}\cup\bigcup_{m\in E_{p,r}}P_m\right),
\qquad
Y_{p,r}=\Omega_p\setminus
       \left(U_{p,r}\cup\bigcup_{m\in E_{p,r}}C_m\right).
\tag{EB9}
\]

For each child \(A_{pm}\), choose its original private point. It lies in branch \(r\), and its pullback is covered by \(C_m\) and by no other active residual original class. Therefore \(X_{p,r}\ne\varnothing\). More strongly, a covering subfamily of EB8 must retain **each** \(C_m\). If one is deleted, its private point cannot be rescued by \(P_m\), a different pair, or \(U_{p,r}\).

Consequently a covering selection using at most one side of each duplicate pair would have to choose all children and no parents. But this all-child family has distinct odd nonunit residual moduli and fewer than \(n\) classes. Minimum cardinality rules out its coverage:

\[
X_{p,r}\ne\varnothing,\qquad Y_{p,r}\ne\varnothing.
\tag{EB10}
\]

Thus the remaining selection is forced before testing whether it covers. A generic search over independent parent/child choices does not supply a further route. A theorem forcing the all-child family to cover under these hypotheses would contradict EB10 and settle the original existence question; no such theorem is supplied here.

## 4. Two exact transports on one common CRT base

Write \(\operatorname{Priv}(A_p)=A_p\setminus\bigcup_{d\ne p}A_d\). Every \(p\)-free original appears either as a parent or inside \(U_{p,r}\), so \(X_{p,r}\) avoids every such original. At the zero first digit, all \(p\)-bearing originals other than \(A_p\) are absent by EB3. Hence

\[
\iota_0(X_{p,r})\subseteq\operatorname{Priv}(A_p).
\tag{EB11}
\]

By EB8, every point of \(Y_{p,r}\) is rescued by at least one parent \(P_m\). A parent is \(p\)-free, so changing only the first \(p\)-digit does not change its membership. Therefore

\[
\iota_0(Y_{p,r})\subseteq
A_p\cap\bigcup_{m\in E_{p,r}}A_m.
\tag{EB12}
\]

The sets in EB9 live in \(\Omega_p\), so \(\iota_0\) has the required domain. Equivalently one may apply the sibling map \(\iota_0\iota_r^{-1}\) to \(\iota_r(X_{p,r})\) and \(\iota_r(Y_{p,r})\). An integer shift that changes other CRT coordinates is not this map.

For any finite nonnegative measure \(\sigma_B\) on \(\Omega_p\), define an explicit product extension by

\[
\sigma=\frac1p\sum_{r=0}^{p-1}(\iota_r)_*\sigma_B.
\tag{EB13}
\]

The same measure then satisfies

\[
\sigma(\operatorname{Priv}(A_p))\ge
\frac1p\sigma_B\left(\bigcup_{r\ne0}X_{p,r}\right).
\tag{EB14}
\]

The union cannot be replaced by a sum: the same base point may belong to several \(X_{p,r}\). For the other side, define

\[
N_{\rm par}(z)=
\sum_{\substack{m\in D:\ p\nmid m,\ pm\in D}}
\mathbf1_{A_m}(\iota_0(z)).
\]

The sets \(E_{p,r}\) are disjoint as \(r\) varies, since the unique original \(A_{pm}\) has only one first \(p\)-digit. A point of \(Y_{p,r}\) contributes at least one parent from that branch's set. Thus, pointwise and after integration,

\[
\sum_{r\ne0}\mathbf1_{Y_{p,r}}(z)\le N_{\rm par}(z),
\qquad
\frac1p\sum_{r\ne0}\sigma_B(Y_{p,r})
\le\int_{A_p}N_{\rm par}(\iota_0^{-1}(x))\,d\sigma(x).
\tag{EB15}
\]

These are joint original-label statements for the specified EB13 law. They neither construct an arbitrary source's product decomposition nor replace its event memberships by independent samples.

## 5. The earlier-ending target has zero killed-source mass

Let \(O_p\) be the original union of labels with largest prime factor strictly below \(p\). All these labels are \(p\)-free, so \(\bar O_p=\iota_r^{-1}(O_p)\) is independent of \(r\). EB11's proof gives

\[
X_{p,r}\subseteq\bar O_p^c.
\tag{EB16}
\]

Let \(H_B\) be uniform probability on the complete base. The raw pre-stage Haar survivor measure \(\eta_H=\mathbf1_{\bar O_p^c}H_B\) therefore has

\[
\eta_H(X_{p,r})=H_B(X_{p,r})\ge\frac{p}{Q}>0.
\tag{EB17}
\]

The normalized Haar survivor law is also positive there. More generally, a pre-stage measure positive on every actual survivor assigns positive mass to \(X_{p,r}\); mere support *inside* the survivor set does not imply this. The pure-survivor kernels in [19-1](../001-064/19-1-same-law-inputs-and-definitions.md), when started with full survivor support, preserve positivity on remaining survivors because their killed density there is \(a(\alpha)>0\). Applying that observation requires the actual initial law and the full-carrier lift, not just an arbitrary supported-law hypothesis.

Now retain only the earlier-ending parent rescues:

\[
Y_{p,r}^{<p}=Y_{p,r}\cap
\bigcup_{\substack{m\in E_{p,r}:\ \operatorname{LP}(m)<p}}P_m.
\tag{EB18}
\]

Already on the base, before changing any digit,

\[
Y_{p,r}^{<p}\subseteq\bar O_p,
\qquad
\iota_0(Y_{p,r}^{<p})\subseteq A_p\cap O_p.
\tag{EB19}
\]

Thus **every** pre-stage killed measure \(\eta\) supported on \(\bar O_p^c\) satisfies

\[
\eta(Y_{p,r}^{<p})=0.
\tag{EB20}
\]

A positive lower bound \(\sum_r\eta(Y_{p,r}^{<p})\ge c_pH(A_p\cap O_p)\), with \(c_p>0\) and \(H(A_p\cap O_p)>0\), is therefore impossible for that same killed law. The failure is a support incompatibility, not an insufficiently strong estimate. After processing stage \(p\), the target \(\iota_0(X_{p,r})\subseteq A_p\) likewise has killed mass zero. Positive pre-stage mass must not be reported as positive post-stage mass.

## 6. What remains between this reduction and report 347

In the extremal system, \(p\) divides every modulus in its largest-prime bucket, and \(p\) itself is present. Hence its sole division-minimal original class is \(A_p\). Under full original Haar,

\[
B_{\min,p}=A_p,\qquad
u_p=H(A_p\cap O_p)=\frac1pH(O_p).
\tag{EB21}
\]

Report 347 forces a positive bounded-ending-prime sum of these original overlap masses. EB14 is a lower bound for private mass in terms of \(X\)-mass, while EB15 bounds \(Y\)-mass above by a parent multiplicity integral. Neither inequality lower-bounds \(X\)-mass using \(u_p\).

A \(p\)-free rescuing parent in EB12 may contain a prime larger than \(p\), so EB12 does not imply earlier-bucket membership. At the final largest support prime \(P\), all such parents do end earlier and \(Y_{P,r}=Y_{P,r}^{<P}\). This does not localize report 347's required mass at that final prime; moreover EB20 still applies to the killed law.

An applicable next estimate would have to use a survivor-side object or an explicit transport between different supports, preserving the actual parent labels and accounting for repeated charges. The existence of private points, the nonempty \(Y\)-sets, and an increasing sequence of ending primes do not provide that quantitative transport.

## 7. Fixed cardinality and self-refinement have different scopes

For an arbitrary irredundant distinct odd whole cover, replacing its numerically largest class \(a\bmod M\) by \(a+Ma_i\bmod Md_i\) preserves coverage and distinctness. The inserted union is exactly the replaced class and all inserted moduli exceed \(M\). Pruning retains every untouched class, by its old private point, and at least one child, by a private point of the replaced class. Thus iteration gives larger maxima on the same prime support and essential new classes with arbitrarily small absolute private mass.

The maximal modulus \(M\) cannot be prime: then all other moduli are \(M\)-free, and coverage on a different first-\(M\)-digit branch would force those other classes already to cover every cofactor state, making the prime class redundant. Thus this refinement never replaces a prime class. Every untouched private set is unchanged before pruning and can only enlarge afterwards; in particular prime-class private sets do not shrink. The small new-label private sets therefore do not refute a bound targeting the prime-private regions in EB14.

This does not preserve EB1. If one child survives, cardinality stays fixed but the sum of moduli increases; if more survive, cardinality increases. The existing Simpson bound in [343, section 2](343-original-prefix-sat-reductions-and-transport-obstructions.md) gives, for every irredundant odd whole cover,

\[
n\ge1+\sum_pH_p(p-1),\quad
Q\le3^{\lfloor(n-1)/2\rfloor},\quad
H(\operatorname{Priv}(A_d))\ge\frac1Q.
\tag{EB22}
\]

The middle bound uses \(p\le3^{(p-1)/2}\) for odd primes; the last uses a private residue in the full period. Unbounded refinement height therefore forces unbounded cardinality. Fixed cardinality, including the hypothetical minimum \(n\), supplies both height and positive private-mass bounds. Self-refinement does not refute them or supply a quantitative improvement of EB14. These are consequences of the retained Simpson result, not new formal declarations.

The only hypotheses asserting global optimality or whole odd coverage in this report are the explicit conditional assumptions above. Finite even covers can check the branch bookkeeping, but cannot certify those hypotheses or serve as counterexamples to statements restricted to odd covers. No Lean build, new frozen result, or resolution of Erdős #7 is claimed.

## 8. Exclusive cofactor defects and the exact affordable repair family

Keep one EB1 representative and all its original phases. Fix a support prime
\(p\) and a nonzero first digit \(c\). Write \(Q=p^HM\), with
\(\gcd(p,M)=1\), so that
\(\Omega_p=\mathbb Z/p^{H-1}\mathbb Z\times\mathbb Z/M\mathbb Z\).
Abbreviate \(E_c=E_{p,c}\) and \(Y_c=Y_{p,c}\). The all-child family
\(\mathcal B_c\) consists of every unique-modulus residual original in
EB8 and every \(C_m\), \(m\in E_c\). Thus

\[
 Y_c=\Omega_p\setminus\bigcup\mathcal B_c.
 \tag{EB23}
\]

Let \(P_m^M\) be the original \(p\)-free class of modulus \(m\) on
\(\mathbb Z/M\mathbb Z\), and put
\[
 O(x)=\{m\in D:p\nmid m,\ x\in P_m^M\},\qquad
 \overline Y_c=\{x:\exists u,\ (u,x)\in Y_c\}.
\]
Whole coverage gives a parent owner at every point of \(Y_c\). Every
\(p\)-free owner whose modulus is outside \(E_c\) is retained in
\(\mathcal B_c\), so
\[
 x\in\overline Y_c\Longrightarrow
 \varnothing\ne O(x)\subseteq E_c,\qquad
 \overline Y_c\cap\overline Y_{c'}=\varnothing\quad(c\ne c').
 \tag{EB24}
\]
The second assertion uses the disjoint original-label sets \(E_c\).
Ownership is independent of the entire \(p\)-tail, not just its first
digit. Consequently, for one common cofactor probability \(\mu\) and
arbitrary branch-dependent probability kernels \(\kappa_c(du\mid x)\),
\[
 \sum_{c\ne0}(\mu\kappa_c)(Y_c)
 \le
 \mu\left(\bigcup_{\substack{m\in D:\,pm\in D\\p\nmid m}}P_m^M\right).
 \tag{EB25}
\]
Indeed, each kernel's conditional defect probability is at most
\(\mathbf1_{\overline Y_c}(x)\), and these indicators have disjoint
supports. Different cofactor marginals cannot be substituted in EB25.
This controls repeated charging, not positive killed-source mass; EB20
still applies.

Identify the same base with \(\mathbb Z/N\mathbb Z\), where \(N=Q/p\),
using EB4's CRT coordinates. Let \(D_c\) be the numerical moduli in
\(\mathcal B_c\), and define
\[
 b=|D_c|,\quad s_c=\sum_{d\in D_c}d,\quad
 S=\sum_{d\in D}d,\quad t=n-b,\quad W=S-s_c.
\]
If \(i_c\) is the number of inactive \(p\)-bearing originals, then
\(b=n-i_c-|E_c|\). Since \(A_p\) is inactive and \(E_c\ne\varnothing\),
\(t\ge2\), and \(W>0\). Every retained modulus divides an original
modulus, so \(D_c\subseteq D\); its \(p\)-free part is exactly the
original \(p\)-free palette.

The vacant divisor palette and the complete affordable label family are
\[
 V=\{e>1:e\mid N,\ e\notin D_c\},
 \qquad
 \mathscr A=
 \{F\subseteq V:|F|\le t-1\}
 \cup
 \left\{F\subseteq V:|F|=t,\ \sum_{e\in F}e<W\right\}.
 \tag{EB26}
\]
All these labels are odd, and \(\mathscr A\) is hereditary. For
\(F\in\mathscr A\), selecting one phase \(a_e\bmod e\) per label gives
a strict EB1 descent exactly when it covers all of \(Y_c\). Retained
classes keep their inherited phases. New phases are independently
selectable across numerical labels; no CRT compatibility between
different replacement classes is required. The full liability is EB23,
not a union of individual private sets. This is the
[PH1--PH2 replacement interface](../arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#1-replace-only-the-region-that-depends-on-the-changed-classes).
Repair using new primes, larger periods, or further changes to retained
classes is outside this fixed palette.

## 9. A fixed palette has an integral obstruction of at most \(2^k\) points

Write \(Y=Y_c\ne\varnothing\), fix an affordable palette \(F\), and put
\(k=|F|\). For \(e\in V\), let \(r_e(z)\in\{0,\ldots,e-1\}\) be the
canonical integer representative of \(z\bmod e\), and let
\(R_e=\{r_e(z):z\in Y\}\). Phases outside \(R_e\) cover no point of
\(Y\), so they are unnecessary for testing repair existence. Failure is
exactly
\[
 \forall a\in\prod_{e\in F}R_e\ \exists z\in Y\quad
 \forall e\in F:\ r_e(z)\ne a_e.
 \tag{EB27}
\]
Equivalently, the phase-choice space is covered by the boxes
\(\prod_{e\in F}(R_e\setminus\{r_e(z)\})\), \(z\in Y\).
Each box retains one actual common point and all its correlated residues.

For nonempty \(F\), choose an inclusion-minimal \(T\subseteq Y\)
still satisfying EB27. For each \(z\in T\), there is a phase tuple
\(a^{(z)}\) covering \(T\setminus\{z\}\), and it must miss \(z\).
The pairs
\[
 A_z=\{(e,r_e(z)):e\in F\},\qquad
 B_z=\{(e,a_e^{(z)}):e\in F\}
\]
are disjoint on their own index and intersect on every cross index.
Each side uses one element of each numerical-label part. Alon's
partitioned set-pairs theorem with all part capacities equal to one
therefore gives
\[
 |T|\le2^k.
 \tag{EB28}
\]
The supplier is Noga Alon, *An Extremal Problem for Sets with Applications
to Graph Theory*, JCTA 40 (1985), 82--89,
[Theorem 1.1 and Corollary 1.2](https://web.math.princeton.edu/~nalon/PDFS/Publications/An%20extremal%20problem%20for%20sets%20with%20applications%20to%20graph%20theory.pdf),
DOI [10.1016/0097-3165(85)90048-2](https://doi.org/10.1016/0097-3165(85)90048-2).
Its bound is \(\prod_i\binom{r_i+s_i}{r_i}\); the present application
has \(r_i=s_i=1\). For \(F=\varnothing\), any one actual point is
already a nonrepair certificate, consistent with \(2^0=1\).

There is a linear-algebra form that preserves positive decisions as well.
Over \(\mathbb Q\), define
\[
 P_z^F(X)=\prod_{e\in F}(X_e-r_e(z)),\qquad
 \rho_F(Y)=\dim_{\mathbb Q}\operatorname{span}\{P_z^F:z\in Y\}.
 \tag{EB29}
\]
At any legal phase tuple, the product is zero exactly when some chosen
class covers \(z\). Select actual points \(T_F\subseteq Y\) whose
polynomials form a basis. Multilinearity gives
\[
 |T_F|=\rho_F(Y)\le2^k,\qquad
 T_F\text{ is covered by }a
 \Longleftrightarrow Y\text{ is covered by }a.
 \tag{EB30}
\]
The forward implication evaluates the linear expression of every
\(P_z^F\) in that basis. It holds for all legal phase tuples, not just
those used to construct a certificate.

In particular, for nonempty affordable \(F\),
\[
 \rho_F(Y)\le |F|\Longrightarrow\text{a strict integral repair exists}.
 \tag{EB31}
\]
Assign different labels to the at most \(|F|\) basis points, choosing
for each assigned label the phase of its point; give the remaining
labels arbitrary phases. This covers \(T_F\), and EB30 covers the full
liability. Thus EB1 forces \(\rho_F(Y_c)\ge|F|+1\) for every such
palette. This rank condition is necessary for nonrepair, not sufficient:
a nonzero minor or a basis alone does not certify that all phase tuples
fail.

## 10. One actual basis preserves the whole lexicographic budget

For the hereditary family \(\mathscr A\) in EB26, form the rational row
\[
 \Phi(z)=\left(\prod_{e\in I}r_e(z)\right)_{I\in\mathscr A}.
 \tag{EB32}
\]
The empty coordinate is one. Choose actual holes \(T\subseteq Y\)
whose rows form a basis of the span of \(\Phi(Y)\). Then
\[
 |T|=\operatorname{rank}_{\mathbb Q}\Phi(Y)\le|\mathscr A|,
 \qquad
 T\text{ is covered}\Longleftrightarrow Y\text{ is covered}
 \tag{EB33}
\]
simultaneously for every \(F\in\mathscr A\) and every phase selection
on \(F\). To see this, expand
\[
 \prod_{e\in F}(a_e-r_e(z))
 =
 \sum_{I\subseteq F}(-1)^{|I|}
 \left(\prod_{e\in F\setminus I}a_e\right)
 \left(\prod_{e\in I}r_e(z)\right).
 \tag{EB34}
\]
Every coordinate on the right occurs in EB32 by heredity. Vanishing
on the basis rows therefore implies vanishing on every row.
The bound is explicitly
\[
 |\mathscr A|=
 \sum_{j=0}^{\min(|V|,t-1)}\binom{|V|}{j}
 +
 \#\left\{F\subseteq V:|F|=t,\ \sum_{e\in F}e<W\right\}.
 \tag{EB35}
\]
No uniform bound on \(|V|\), \(t\), or the cost of obtaining these
actual rows is asserted.

A negative certificate needs actual membership \(T\subseteq Y\) and,
for every affordable palette and every relevant phase tuple, a listed
point missed by that tuple. A positive certificate that checks only
\(T\) additionally needs the spanning implication EB33. This distinction
prevents a selected list of private witnesses from replacing the joint
liability.

For a fixed \(F\), phase menus may further be reduced to
\(\{r_e(z):z\in T_F\}\): a phase absent from these menus covers no
basis point and can be replaced without losing basis coverage. Hence a
fixed \(k\)-label negative certificate needs at most \(2^{k^2}\)
phase tuples after EB30. One fixed-palette certificate does not obstruct
the other members of \(\mathscr A\). These are applications of finite
linear algebra and Alon's theorem, not new general set-pairs results.

## 11. The actual basis supports rounding with both EB1 costs

For each vacant \(e\) and phase \(a\bmod e\), let \(x_{e,a}\ge0\).
For an integer \(k\ge0\), impose
\[
 x\in P_k\quad\Longleftrightarrow\quad
 \sum_a x_{e,a}\le1\quad(e\in V),\qquad
 \sum_{e,a}x_{e,a}\le k.
 \tag{EB36}
\]
For any fixed actual finite test set \(T\), define
\[
 U_T(x)=\sum_{z\in T}\prod_{e\in V}(1-x_{e,r_e(z)}),
 \qquad C(x)=\sum_{e,a}e\,x_{e,a}.
 \tag{EB37}
\]
For every \(x\in P_k\) and \(\lambda\ge0\), there is an integral
selection \(\mathcal R\), using at most \(k\) distinct vacant moduli,
such that
\[
 \left|T\setminus\bigcup\mathcal R\right|
 +\lambda\sum_{A\in\mathcal R}\operatorname{mod}(A)
 \le U_T(x)+\lambda C(x).
 \tag{EB38}
\]

This is the coverage specialization of pipage rounding. The reusable
source is Calinescu--Chekuri--Pál--Vondrák, *Maximizing a Monotone
Submodular Function Subject to a Matroid Constraint*,
[author manuscript, Lemma 3.5, pp. 15--16, and Section 5, p. 22](https://theory.stanford.edu/~jvondrak/data/submod-matroid.pdf).
The following specialization keeps the linear cost penalty explicit;
it does not assume that adding a knapsack constraint preserves
integrality.

Fix \(q_e=\sum_a x_{e,a}\). The objective \(U_T+\lambda C\) is affine
in each label's phase block, so concentrate that block on a minimizing
phase without increasing the objective. There is now one selected
class \(A_e\) and one mass \(q_e\in[0,1]\) per label. Add empty zero-cost dummy
choices to make the total mass exactly \(k\). Along an exchange
\(q_i+\delta,q_j-\delta\), the second derivative of the objective is
\[
 -2\sum_{z\in T\cap A_i\cap A_j}
 \prod_{\substack{\ell\ne i,j\\z\in A_\ell}}(1-q_\ell)\le0.
\]
An endpoint therefore does not increase it and makes another coordinate
integral. An integer total leaves no isolated fractional coordinate;
iteration terminates, and the dummies are discarded. At integral
coordinates the objective is exactly EB38's left side.

Now use the actual basis \(T\) from EB32--EB33, with the same
\(\mathscr A\), \(t\), and \(W\). Either of the following is sufficient
for a strict repair of the complete \(Y_c\):
\[
 x\in P_{t-1},\quad U_T(x)<1,
 \tag{EB39}
\]
or
\[
 x\in P_t,\quad U_T(x)+C(x)/W<1.
 \tag{EB40}
\]
For EB39 take \(\lambda=0\); the integer number of uncovered basis
points is zero, and the output palette is affordable by cardinality.
For EB40 take \(\lambda=1/W\); again that integer is zero, and the
added modulus sum is strictly less than \(W\). The output palette
therefore belongs to \(\mathscr A\) in both cases, so EB33 upgrades
coverage of \(T\) to coverage of all \(Y_c\). Retained phases and
one-class-per-numerical-modulus constraints are unchanged.

One may use the simpler sufficient estimate
\[
 U_T(x)\le
 \sum_{z\in T}\exp\left(-\sum_{e\in V}x_{e,r_e(z)}\right).
 \tag{EB41}
\]
Ordinary fractional covering loads at least one do not imply EB39.
The threshold uses a supplied quantitative witness and a certified
actual basis. Merely choosing a few representative holes does not
justify it.

The unrestricted missing implication remains arithmetic: the same
hypothetical odd EB1 cover must force some actual branch and affordable
palette satisfying EB31, or some actual basis and fractional witness
satisfying EB39 or EB40, or another legal strict repair. None of those
existence statements follows here from EB24's disjoint cofactor
defects. Disjoint point sets need not have independent polynomial row
spaces. Nor does the \(2^k\) obstruction bound yield a bounded search
over arbitrary original supports and heights.

Optimizing EB39--EB40 without an arithmetic bound is still an exact
nonlinear repair problem: an integral strict repair itself supplies a
valid \(x\), and EB38 supplies the reverse conversion. If \(V\) is
empty, \(\mathscr A=\{\varnothing\}\) and one actual point is already a
complete obstruction; no repair label is created by compression.
These applications preserve the full original liability and both costs,
but establish neither a universal improving replacement nor unrestricted
noncoverage. They are ordinary mathematical deductions and carry no
new Lean verification or originality claim.

## 12. Parent periods give an explicit sufficient repair budget

Keep the whole-cover hypotheses and the notation of Sections 8--11. For
one branch write \(E=E_c\), \(Y=Y_c\), and retain \(t=n-b\) for the
number of available repair slots. In particular \(t\) is not the number
\(i_c\) of inactive originals: \(t=i_c+|E|\).

The numerical palette can be read from the original \(p\)-chains.
For a \(p\)-free \(m\in D\), divisor closure makes its original labels
\(m,pm,\ldots,p^{h_m}m\). Its \(p\)-free residual label \(m\)
is always occupied, while for \(j\ge1\),
\[
 p^jm\in D_c\quad\Longleftrightarrow\quad
 j+1\le h_m\ \text{ and }\ a_{p^{j+1}m}\equiv c\pmod p.
\]
The same positive-\(j\) rule applies to \(m=1\). Hence a
\(p\)-bearing residual label \(e\) with \(pe\in D\) is occupied
in exactly one nonzero branch and vacant in the other \(p-2\). An
occupied residual chain need not be an initial segment. If \(n_p\)
counts all original \(p\)-bearing labels and \(H_c\) counts those
with \(p\)-exponent at least two and first digit \(c\), then
\(b_c=n-n_p+H_c\) and \(t=n_p-H_c\). These are exact inventory
identities, not permission to alter any inherited phase.

For \(L\mid N\), the image of the complete original parent
\(P_m=a_m\bmod m\) under reduction modulo \(L\) is
\[
 R_m(L)=\{v\bmod L:v\equiv a_m\pmod{\gcd(L,m)}\},\qquad
 |R_m(L)|=\frac{L}{\gcd(L,m)}.
 \tag{EB42}
\]
CRT proves the equality of the image with this entire residue class.
Define the actual union of these projected parent classes and its
phase-independent upper bound by
\[
 R_c(L)=\bigcup_{m\in E_c}R_m(L),\qquad
 q_c(L)=\sum_{m\in E_c}\frac{L}{\gcd(L,m)}.
 \tag{EB43}
\]
Whole coverage is used at precisely the inclusion
\(Y_c\bmod L\subseteq R_c(L)\), through EB8 and EB23. Consequently
\(|Y_c\bmod L|\le |R_c(L)|\le q_c(L)\). This inclusion is not a
consequence of nonempty collision sets alone.

If an affordable palette \(F\) consists of divisors of \(L\) and
has at least \(|R_c(L)|\) labels, it repairs all of \(Y_c\). Assign
different labels \(e_v\in F\) to the residues \(v\in R_c(L)\),
and use the phase \(v\bmod e_v\). Since \(e_v\mid L\), the chosen
class contains the entire \(L\)-fiber of \(v\). Every liability
point is therefore covered. Remaining labels may be omitted; heredity
of the affordable family preserves the budget. This is a direct
full-liability assignment using the existing replacement interface,
not a new general matching or rank theorem. The parent labels remain
occupied throughout.
The whole-parent digit construction is already available in
[report 385, Section 200, LP2--LP5](../arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#200-a-vacant-lower-prime-layer-gives-a-whole-cover-descent);
the partial-height version retains its private-fiber obligation in
[Section 240, PFV5](../arithmetic/350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#240-private-fibre-vacancy-is-the-exact-partial-height-strict-cut).
The application here makes the all-child vacancy and both EB1 budgets
explicit; it does not supply another repair theorem.

For a numerical consequence, put
\[
 V_c(L)=\{e>1:e\mid L,\ e\notin D_c\},
 \qquad V_c(L)=\{e_1<\cdots<e_v\}.
\]
Every hypothetical EB1 cover must satisfy
\[
 q_c(L)<t\Longrightarrow |V_c(L)|<q_c(L),
 \tag{EB44}
\]
and
\[
 q_c(L)=t,\quad |V_c(L)|\ge t
 \Longrightarrow \sum_{j=1}^{t}e_j\ge W.
 \tag{EB45}
\]
Indeed, a violation supplies \(q_c(L)\) distinct vacant divisors of
\(L\), affordable by cardinality or by the strict sum bound, and
\(q_c(L)\ge|R_c(L)|\). The preceding assignment contradicts EB1.
Using \(|R_c(L)|\) instead of \(q_c(L)\) gives the corresponding
stronger, phase-dependent test. Projected parent classes from different
branches need not be disjoint at a coarse \(L\); their counts cannot
be shared without another complete-liability argument.

The ownership premise is essential even for this numerical consequence.
The odd divisor-closed noncover
\[
 0\bmod3,\ 1\bmod9,\ 0\bmod5,\ 1\bmod25,\ 6\bmod125,
 \ 11\bmod15,\ 2\bmod75,\ 127\bmod375
\]
has, at \(p=3,c=1\), \(E_c=\{125\}\) and retained family
\(\{0\bmod3,0\bmod5,1\bmod25,2\bmod125\}\). Its slot
budget is four. For \(L=N=375\), one has \(q_c(L)=3\) and
\(V_c(L)=\{15,75,375\}\). But the actual liability has
\(2(125-25-5-1)=188\) points, only two of them in the parent
\(6\bmod125\). The three vacant slots can cover that parent;
they do not cover the full liability by the profile assignment above.
Thus EB44 is a genuine consequence of whole-cover ownership, not a
numerical identity forced by chain occupancy alone.

Releasing an occupied label does not automatically improve this coarse
count. If \(A_e\in\mathcal B_c\) is removed, its additional liability
is \(J_e=A_e\setminus\bigcup(\mathcal B_c\setminus\{A_e\})\),
disjoint from \(Y_c\). The exact new liability and budgets are
\(Y_c\sqcup J_e\) and \((t+1,W+e)\). Bounding \(J_e\) by the
entire released class replaces \(q_c(L)\) by
\(q_c(L)+L/\gcd(L,e)\), while the vacant-divisor count increases
by at most one. Since \(L/\gcd(L,e)\ge1\), neither the slot-minus-
profile gap nor the vacancy-minus-profile gap improves at fixed \(L\).
This is a limitation of paying for the whole released cylinder. A gain
could still come from the actual joint-private set \(J_e\), overlap
of its projected profiles with existing liability profiles, or the
strict modulus-sum boundary. Counting freed labels alone omits that
liability; the full replacement rule remains PH1--PH2.

### The exact cost in the polynomial formulation

For a nonempty affordable palette \(F\), let \(k=|F|\) and
\(L_F=\operatorname{lcm}(F)\). On a full parent class write
\(z=a_m+mu\), with \(u\bmod N/m\). The residue function
\(r_e(a_m+mu)\) has period \(e/\gcd(e,m)\). Thus all squarefree
\(F\)-features have common period
\[
 \operatorname{lcm}_{e\in F}\frac{e}{\gcd(e,m)}
 =\frac{L_F}{\gcd(L_F,m)}.
\]
There are at most this many different evaluation rows on the parent,
and at most \(2^k\) feature coordinates. Since the full liability
lies in the union of these parents, EB29--EB30 give
\[
 \rho_F(Y_c)\le
 \sum_{m\in E_c}
 \min\left\{2^k,\frac{L_F}{\gcd(L_F,m)}\right\}.
 \tag{EB46}
\]
The bound uses all full-parent rows as an outer approximation to the
actual liability rows. Its being greater than \(k\) does not rule out
an actual low-rank repair.

There is also a legitimate way to separate different branches in an
evaluation matrix. Let
\(h_c(z)=\sum_{m\in E_c}\mathbf1_{P_m}(z)\). On \(Y_d\), EB24
gives \(h_c=0\) for \(c\ne d\) and \(h_c\ge1\) for \(c=d\).
Multiplying each branch's feature columns by \(h_c\), then evaluating
on \(\bigcup_dY_d\), gives a block diagonal matrix whose rank is the
sum of the branch ranks: within each block every row is multiplied by
a nonzero rational number. This reuses ordinary block-rank and row-scaling
facts. Its cost is the expansion
\[
 h_c\phi_I=\sum_{m\in E_c}\mathbf1_{P_m}\phi_I.
\]
It introduces occupied-parent indicators, not additional legal repair
slots. Charging each indicator-feature space by EB46 adds its cost
along with its rank and supplies no cross-branch saving by itself.

Oddness makes the limitation of this full-parent bound explicit. For
every vacant \(e\) and every \(m\in E_c\), one has \(e\nmid m\):
otherwise divisor closure makes \(e\) an original \(p\)-free label,
already occupied in \(D_c\). If \(\ell\) is the smallest prime
dividing \(N\), then
\[
 \frac{e}{\gcd(e,m)}\ge\ell\ge3.
\]
For EB46's right side to be at most \(k\), it is necessary that
\(k\ge\ell|E_c|\). In fact it is at least
\(|E_c|\min\{2^k,\ell\}\), and the alternative minimum \(2^k\)
already exceeds \(k\). Affordability would therefore require
\(t\ge\ell|E_c|\), or \(i_c\ge(\ell-1)|E_c|\). These are
limitations of this particular upper bound, not necessary conditions
for every repair. Actual parent overlaps in EB43 or relations specific
to \(Y_c\) can give a sharper test.

No argument here forces an EB1 branch to violate EB44--EB45 or to make
EB46 at most \(|F|\). The missing conclusion remains a supplied
affordable repair on one actual whole-cover branch.

## 13. Odd local structure alone does not fund either ternary repair

Consider the single fixed family
\[
 \mathcal C=\{0\bmod3,\ 0\bmod5,\ 0\bmod7,\ 2\bmod9,
 0\bmod11,\ 0\bmod13,\ 1\bmod15,\ 8\bmod21\}.
 \tag{EB47}
\]
Its eight moduli have sum \(84\) and lcm \(Q=45045\). They are
distinct odd nonunits, form a divisor-closed set, and have initial
odd-prime support. Comparable classes are disjoint. In the displayed
order, private integers are \(3,5,7,2,22,13,1,8\). Their membership
and privacy follow by direct reduction in the eight named moduli.
The reciprocal sum is \(48172/45045>1\), but the integer 4 is
uncovered. Thus this is explicitly a noncover, not an EB1 representative.

Set \(p=3\), \(N=Q/3=15015\), and use the actual common CRT carrier
with tail coordinate \(z\bmod3\) and cofactor coordinate
\(z\bmod5005\). The source inserts \(c+3(z\bmod3)\) modulo 9 and
preserves every cofactor coordinate. The two all-child retained families
are
\[
 \mathcal B_1=\{1\bmod5,0\bmod7,0\bmod11,0\bmod13\},
\]
\[
 \mathcal B_2=\{0\bmod3,0\bmod5,1\bmod7,0\bmod11,0\bmod13\}.
 \tag{EB48}
\]
Their collision sets are \(E_1=\{5\}\) and \(E_2=\{7\}\).
Their complete complements \(Y_c=(\mathbb Z/N\mathbb Z)\setminus
\bigcup\mathcal B_c\) have the following exact data, by CRT counting:

| Branch | Inactive originals \(i_c\) | Retained count \(b_c\) | Slots \(t\) | Sum budget \(W\) | \(|Y_c|\) | Density |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 3 | 4 | 4 | 48 | 8640 | \(576/1001\) |
| 2 | 2 | 5 | 3 | 45 | 5760 | \(384/1001\) |

Neither retained family can be repaired within its slot budget, even
allowing arbitrary new prime support and heights. The four smallest
unused odd nonunit moduli for \(\mathcal B_1\) are \(3,9,15,17\).
For \(\mathcal B_2\), the three smallest are \(9,15,17\). Any
legal repair with at most the respective number of distinct moduli
has union density at most the corresponding reciprocal sum. But
\[
 \frac{576}{1001}-
 \left(\frac13+\frac19+\frac1{15}+\frac1{17}\right)
 =\frac{4204}{765765}>0,
\]
\[
 \frac{384}{1001}-
 \left(\frac19+\frac1{15}+\frac1{17}\right)
 =\frac{112579}{765765}>0.
 \tag{EB49}
\]
For any proposed palette, this density argument is exact counting on
the common period obtained by adjoining its moduli to \(N\). It does
not restrict the repair to divisors of \(N\); it already allows the
new prime 17 and the higher power \(9\nmid N\). The sum budget is
not needed for the exclusion. The retained family is kept fixed.

Even restricting to parent-owned points does not make every affordable
palette low rank. For \(F=\{35,55\}\), the four actual points
\(750,540,1080,870\) lie in \(Y_1\cap P_5\). Their residue pairs
are \((15,35),(15,45),(30,35),(30,45)\), and their feature matrix is
\[
 \begin{pmatrix}
 1&15&35&525\\1&15&45&675\\
 1&30&35&1050\\1&30&45&1350
 \end{pmatrix},\qquad \det=-22500.
 \tag{EB50}
\]
Thus this fixed palette has \(\rho_F(Y_1)=4>2\). On these four
points, rounding restricted to the same palette has
\[
 U_T=(2-\alpha)(2-\beta)\ge1,\qquad
 \alpha=x_{35,15}+x_{35,30}\le1,\quad
 \beta=x_{55,35}+x_{55,45}\le1.
 \tag{EB51}
\]
These four rows certify the fixed palette; they are not asserted to be
a basis for every affordable palette. EB49 supplies the separate
full-liability nonrepair proof.

The whole-cover ownership hypothesis fails explicitly. Only 2160 of
the 8640 points of \(Y_1\) belong to \(P_5\), and only 960 of the
5760 points of \(Y_2\) belong to \(P_7\). The two cofactor
projections each have size 2880 and overlap in 1800 points. In
particular \(4\in Y_1\cap Y_2\) has no original \(3\)-free parent
owner. This prevents applying EB24 or EB42--EB46 to the full liabilities
as if they were parent-covered. The example excludes repair conclusions
from these weaker local properties alone, including a density sum above
one and two nonempty collision sets. It does not exclude repairs that
also change retained classes or establish anything about a hypothetical
whole-cover EB1 representative. All deductions in Sections 12--13 are
ordinary finite mathematics; no new Lean verification is claimed.
