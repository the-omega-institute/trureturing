[Index](../../../../Problems/erdos-7-odd-covering-systems.md)

# Full density and large-prime continuation for common-spine books

**Full-density theorem.** Let a finite family have distinct odd moduli
greater than one. Suppose its primes other than 3 and 5 have a partition
into \(N\) nonempty private pages, each containing at most two primes,
such that every modulus is supported on the common spine \(\{3,5\}\)
and at most one page. Classes supported only on the spine are included
once. Then the full original Haar survivor proportion is greater than
\[
 \varepsilon_N=
 \frac{968925187}{30375000000000}
 \left(\frac{45539483789}{1528808537470752}\right)^N>0.
 \tag{BD1}
\]
This bound is uniform in the prime labels, original finite heights,
residues, and number of moduli. The integer \(N\) counts the chosen
nonempty private pages, not moduli, exponents, or auxiliary coordinates.
For a spine-only family use \(N=0\).

**Large-prime continuation.** Fix the head prime set \(P\) and its
permitted page partition. A computable cutoff
\(B_0(P,N)\ge\max(\{286\}\cup P)\) allows any finite collection of
additional primes greater than \(B_0\), with arbitrary finite powers,
residues, and support sizes, without producing a cover. Only the
head-only classes must satisfy the book condition. Tail-touching classes
may join any number of head pages.

The density statement strengthens
[Chapter 36](36-common-spine-books-of-four-prime-pages.md), which bounds
the proportion of extendible spine words. Its proof also needs volume
inside the core and pointwise private-page fibres. The continuation uses
the existing bridge of
[Chapter 33](33-seven-small-primes-with-an-unrestricted-large-prime-tail.md)
in the same way as
[Chapter 34](34-uniform-head-density-from-thick-block-domains.md).
These are ordinary mathematical deductions with exact rational
constants and the same inherited source and analytic premises. No new
Lean verification or solution of unrestricted Erdős #7 is claimed.

## 1. Thicken the actual page fibres in one common law

Retain Chapter 36's actual core choice. It has zero, one, or two private
pages: it includes every page containing 7 or 11. Thus every remaining
page has real smaller prime \(q\ge13\) and larger prime \(r\ge17\),
after the dummy padding described below when necessary.

For one remaining page, use its actual pure-avoiding domains \(V_q,V_r\)
and product law
\[
 \nu=H_q(\cdot\mid V_q)\otimes H_r(\cdot\mid V_r).
\]
At each complete original spine word \(x\), let \(R_x\) avoid the
actual shallow classes at that page's chosen rectangle, and put
\(\nu_x=\nu(\cdot\mid R_x)\). Chapter 36 gives
\(\nu(R_x)\ge Z>0\) for every \(x\).

For original labels outside that rectangle define the actual conditional
load
\[
 u(x)=\sum_{\ell\text{ deep}}
  \mathbf1_{\{x\text{ matches the spine part of }\ell\}}
                         \nu_x(C_\ell).
 \tag{BD2}
\]
The proof of (BK5), before using the indicator of total blockage, yields
\[
 \int u(x)\,dH_{35}(x)\le g(q).
 \tag{BD3}
\]
Indeed, (BK4) bounds each actual query under the same \(\nu_x\), and
integration of its original spine cylinder gives (BK6). Both zero
exponent axes are retained. This bounds the actual averaged load, not
only the measure of words with no extension.

Write
\[
 \delta=\frac{968925187}{2025000000000},\qquad S=\frac{21}{200},
 \qquad
 \eta=\frac{\delta}{2S+\delta}
       =\frac{968925187}{426218925187}.
 \tag{BD4}
\]
Remove the stronger bad-spine set
\(W=\{x:u(x)>1-\eta\}\). Markov's inequality gives
\[
 H_{35}(W)\le\frac{g(q)}{1-\eta}.
 \tag{BD5}
\]
For every \(x\notin W\), the union of all matching deep labels has
\(\nu_x\)-mass at most \(1-\eta\). Hence the actual full private
survivor fibre has original Haar proportion at least
\[
 H_q(V_q)H_r(V_r)\,\nu(R_x)\eta.
 \tag{BD6}
\]
This is a pointwise statement at the same spine word, using the same
actual shallow conditional law as the cost estimate.

The minimum \(Z\) among the 29 finite rows of Chapter 36 is
\(94/6165\), attained at the row with smaller prime 137. Its analytic
tail has \(Z\ge1/2\). The selected dominating caps therefore give
\(\nu(R_x)\ge94/6165\) for every remaining page. Also
\[
 H_q(V_q)H_r(V_r)
 \ge\frac{11}{12}\frac{15}{16}=\frac{55}{64}.
\]
Consequently (BD6) has the uniform lower bound
\[
 a:=\eta\frac{94}{6165}\frac{55}{64}
   =\frac{45539483789}{1528808537470752},\qquad 0<a<1.
 \tag{BD7}
\]
The numerical value is approximately \(2.979\times10^{-5}\).

## 2. The same core pays the stronger bad sets

Let \(\mu\) be the actual core submeasure in the applicable case of
Chapter 36, and let \(m\) be its certified lower mass. It avoids all
original core classes and has joint spine marginal at most \(H_{35}\).
Let \(G\) be the sum of the safe fees \(g(q)\) of its actual remaining
pages. Their minimum primes are distinct and exclude the actual core's
private primes. Chapter 36's same case split and fee discounts give
\[
 G<S,\qquad m-G>\delta.
 \tag{BD8}
\]
For each of the 13 split-core ranges this is the corresponding source
mass minus the remaining fee sum; the strict total fee bound makes it
strict even for the row whose displayed margin equals \(\delta\).
The anchor-only and one-page cores have larger margins.

Delete every \(W_i\) from this same core measure, according to its
spine coordinates. The whole deletion costs at most \(G/(1-\eta)\).
Since
\[
 \frac{\eta}{1-\eta}S=\frac\delta2,
\]
the remaining core submeasure has mass greater than
\[
 m-G-\frac{\eta}{1-\eta}G>\frac\delta2.
 \tag{BD9}
\]
All remaining pages simultaneously have the pointwise fibre bound
\(a\) at each spine word supporting this restricted measure. No core
or page survivor measure is renormalized.

## 3. A full joint density bound for the core

A bound for the joint spine marginal alone would not control the
volume in private core coordinates. Here the actual source construction
supplies the additional bound
\[
 \mu\le D_*H_{\mathrm{core}},\qquad D_*:=\frac{15}{2}.
 \tag{BD10}
\]
The initial anchor measure is an unnormalized Haar restriction, with
density at most one. Each normalized private-coordinate kernel has
its stated pointwise conditional density cap, and deletions only
decrease the density. Multiplying these **conditional** caps gives a
full joint bound; this is not multiplication of separate marginal caps.

The anchor-only core has cap one. The source four-prime core has cap
\((3/2)(5/3)=5/2\). For the actual six-prime core
\((3,5,7,11,u,v)\), where \(u\ge13,v\ge17\), the thresholds
\((2,4,4,8)\) give
\[
 D(u,v)=\frac32\frac53\frac{u-1}{u-5}\frac{v-1}{v-9}
 \le\frac32\frac53\frac32\,2=\frac{15}{2}.
 \tag{BD11}
\]
Haar-preserving coordinate normalizations and projection from source
heights to the complete original finite heights preserve these bounds.

When the four-prime core is transported to a larger actual private
pair, use Chapter 36's **averaged** private prefix injections, which
fix the full spine. For each such injection \(F\), construct the
source measure \(\mu_F\) and apply its full bound before averaging:
\[
 \mathbb E_F(F_*\mu_F)(A)
 \le\frac52\mathbb E_F H_{\mathrm{source}}(F^{-1}A)
 =\frac52 H_{\mathrm{target}}(A).
 \tag{BD12}
\]
For each fixed source private word its image is uniform on the target
private coordinates, while the spine retains its original Haar law.
The source measure may depend on \(F\); the inequality applies
separately for every \(F\) before taking the average. Mass and original
avoidance are retained. A single fixed injection is not asserted to
preserve this full Haar bound.

Let \(C\) be the set of core tuples avoiding its original classes and
all the stronger outside-page bad-spine sets. By (BD9)--(BD10),
\[
 H_{\mathrm{core}}(C)>\frac{\delta/2}{15/2}
 =\frac\delta{15}.
 \tag{BD13}
\]
This concerns full core tuples, not just the projection of those tuples
onto the spine.

## 4. Integrate the private fibres and remove padding

Suppose \(M\) pages remain outside the chosen core. For every tuple
in \(C\), each of those pages has original private Haar fibre at least
\(a\), at precisely that tuple's spine word. The page coordinate sets
are disjoint, so their conditional product fibre has measure at least
\(a^M\). Integrating over \(C\) gives full survivor proportion
\[
 H(U)>\frac\delta{15}a^M
       \ge\frac\delta{15}a^N=\varepsilon_N,
 \tag{BD14}
\]
because \(M\le N\) and \(0<a<1\). No independent choice of
separately optimal spine words or core tuples is used.

For a page with one real private prime, adjoin one fresh dummy prime
larger than every original prime and 149. Give it a full coordinate
domain and exponent zero in every original label. All dummy primes are
different. This adds a coordinate to the same page, not a new page.
In the remaining pages the minimum prime stays real and at least 13;
the dummy pure-domain density is one, so the same lower bound
\(55/64\) remains valid.

Original avoiding sets are independent of every dummy coordinate.
Their augmented Haar proportions are therefore exactly their original
Haar proportions, globally and in each fixed real fibre. Projecting
away the dummies preserves (BD14), even if the auxiliary source measure
used to prove it was not itself independent of them. Absent spine
coordinates can likewise be added without original constraints and
then removed. All source constructions use heights resolving the
whole original family, with the harmless source-anchor height padding
of Chapter 33 when required.

Thus (BD1) is a bound for the original complete Haar volume, uniform
over prime labels, heights, and residues. Its decay with \(N\) is
explicit; no lower bound independent of the number of pages is claimed.

## 5. Fixed-head continuation to unrestricted large primes

Fix the actual head prime set \(P\) and a partition of its private
primes into \(N\) pages. Only classes supported entirely on \(P\)
are required to obey the book condition. Missing events or unused
head coordinates are allowed; adjoining such free coordinates does
not change the survivor proportion. Equivalently, if fewer actual
pages occur, their stronger bound implies (BD1) for this larger \(N\).

At head heights resolving the entire larger family, let \(U_H\)
avoid all original head-only classes, and take
\[
 \mu_H=H_P|_{U_H}.
\]
Uniform lifting to these heights preserves density, so
\[
 \mu_H(X)>\varepsilon_N,\qquad \mu_H\le H_P.
 \tag{BD15}
\]
The dummy coordinates have already been removed. They do not enter
\(P\), the head moment, or the cutoff.

Use Chapter 33's existing homogeneous joint-load continuation with
joint density cap \(D=1\) and
\[
 M_2(P)=\prod_{p\in P}\left(1+\frac{3p-1}{(p-1)^2}\right).
\]
For integers \(\ell\ge6\) put \(B=3^\ell\),
\(c_\ell=(2\ell^2+1)/(2\ell^2-1)\), and
\[
 \tau_7(B,\ell)=
 \frac{c_\ell^7}{B}\left(\frac B{B-3}\right)^2
 \sum_{h=0}^7\frac{7!}{(7-h)!\ell^h}.
 \tag{BD16}
\]
Increase \(\ell\) until
\[
 B\ge\max(\{286\}\cup P),\qquad
 M_2(P)\tau_7(B,\ell)<\frac{\varepsilon_N}{2}.
 \tag{BD17}
\]
This is an effective exact-rational search. It terminates because
\(3^{-\ell}\) tends to zero and all the other factors in (BD16)
remain bounded. Let its first successful \(B\) be \(B_0(P,N)\).
The original analytic requirements, including \(B\ge286\),
\(\ell\ge4\), and \(3^\ell\le B\), are then satisfied.

If every original prime outside \(P\) is greater than \(B_0\),
Chapter 33 bounds the total weighted tail deletion by less than
\(\varepsilon_N/2\). It processes every tail-touching original
class, including pure tail classes, using one sequence of normalized
full-coordinate kernels. Its finite positive measure retains a
complete avoiding tuple. No restriction is imposed on how many head
pages a tail class joins or how many further primes it contains.

The final weighted reserve is not identified with the same numerical
lower bound for final Haar density. The head \(P\) and partition are
fixed before selecting the cutoff. This is a sufficient gap condition
for continuation, not a statement that an arbitrary family already
has no primes in the gap. The argument inherits Chapter 33's stated
analytic prime-product premise and verification boundary.

## 6. Exact constants and retained proof obligations

The program
[`spine_book_density_certificate.py`](../frontier/cover-geometry/spine_book_density_certificate.py)
reads the existing Chapter 36 certificate and checks its SHA-256,
the common margin \(\delta\), minimum shallow residual, threshold
inflation, pure-domain product, core kernel-cap products, and (BD1)'s
two rational factors. Its
[`output`](../frontier/cover-geometry/spine_book_density_certificate.json)
records the exact constants. It does not rerun geometry or assert
machine verification of the conditional-law or full-density proofs.

The additional mathematical steps are (BD3)'s actual load estimate,
the simultaneous threshold change in the same core measure, the full
joint bound including averaged private transport, and integration of
pointwise private fibres. These supply volume information absent from
a bare existential extension statement. The tail step then uses the
already stated bridge, with every original modulus, residue, and
height retained.
