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

The normalized Haar survivor law is also positive there. More generally, a pre-stage measure positive on every actual survivor assigns positive mass to \(X_{p,r}\); mere support *inside* the survivor set does not imply this. The pure-survivor kernels in [19-1](../19-1-same-law-inputs-and-definitions.md), when started with full survivor support, preserve positivity on remaining survivors because their killed density there is \(a(\alpha)>0\). Applying that observation requires the actual initial law and the full-carrier lift, not just an arbitrary supported-law hypothesis.

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
