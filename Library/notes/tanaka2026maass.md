---
bibkey: tanaka2026maass
authors: Daichi Tanaka
year: 2026
title: Explicit Construction of Maass Wave Forms and Their Petersson Inner Products
doi: 10.48550/arXiv.2601.21588
claim: Theorem 1.1 constructs Maass cusp forms from the specified primitive real-quadratic Hecke characters, including parameter zero; it does not supply a missing golden ring-class character.
strata_touched: []
license: citation-only
triage: anchor
---

# Real-quadratic Hecke construction and the complete golden tower

## Primary source and exact scope

Daichi Tanaka, *Explicit Construction of Maass Wave Forms and Their Petersson
Inner Products*, arXiv:2601.21588v3, revised February 3, 2026.

https://arxiv.org/abs/2601.21588
https://arxiv.org/html/2601.21588v3

The source passages used here are equation (1.1), the cosine/sine definition
immediately following it, Theorem 1.1, and the subsequent discussion of
spectral parameter zero. The theorem assumes a primitive Hecke character of
specified archimedean type that does not factor through the norm and a
Dirichlet character. It constructs a Maass cusp form at the displayed
quadratic-discriminant and conductor level. For the finite odd-order
anticyclotomic characters in the WSS dossier, the real components are
trivial, the parameter is zero, and the non-norm condition is satisfied.

The source's cosine form has first exponential Fourier coefficient one half.
The WSS dossier uses twice that form, with first exponential coefficient one.
The complete-tower arguments below depend on these coefficients and their
Hecke eigenvalues. No Petersson norm formula or earlier normalization
correction is an input to CTG.

## Actual mathematical consumer

`Problems/wall-sun-sun-golden-unit-lift.md`, ROC and CTG.1, starts with an
ACTUAL golden ordinary ring-class character eta of order p^k. This is an
arithmetic hypothesis, equivalent in ROC to h_p>=k+1. Its nontrivial powers
have primitive conductors appropriate to their orders. Apply the cited
construction at each primitive conductor and then include the unscaled
oldvector g(z) at the common level. This gives the complete tower, including
all smaller nontrivial p-power character orders.

CTG.1-CTG.6 then prove, by integer polynomial and trace-dual arguments, the
following statements about that already-existing tower:

- its good-Hecke order is Z[X]/Q_k, where
  Q_k=product_(j=1)^k Psi_(p^j), with Q_k(2)=p^k;
- adjacent primitive packets are glued over a nonreduced quotient of
  characteristic p, rather than being an integral direct product;
- its scalar Eisenstein congruence module is Z/p^k, although every individual
  primitive packet has module Z/p;
- a specified integral trace combination attains precisely this congruence
  depth, and its normalized mod-p^r class exists exactly for r<=k.

These complete-tower formulas are proved in the dossier and are not
attributed to Tanaka. Their independent priority is unconfirmed. They do not
construct eta at a new target prime and do not prove a new WSS family.

The existing arithmetic source
`D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.lean` already states the
integer-image and unique-reconstruction theorem for modulus 2n+3, without a
primality hypothesis. CTG.3 identifies the actual complete-tower trace matrix
with that template at 2n+3=p^k. Its companion Scribe records this ordinary
application and the cited ambient construction. The spectral identification
is not an additional kernel-certified conclusion of that Lean source.

## Single-prime reconstruction in HCR

The same existing WSS owner, HCR.1-HCR.7, also retains one primitive packet
rather than the complete tower. After an actual generator-rotation auxiliary
prime ell has been selected in the already-existing class field, its ideal
coefficients are P_n(t), where P_0=1, P_1=X and P_(n+1)=XP_n-P_(n-1).
They are the classical U_n(X/2), with generating function
1/(1-XZ+Z^2). The polynomial identity is NIST DLMF 18.12.10:
https://dlmf.nist.gov/18.12.E10

The ambient Fourier interpretation comes from Tanaka's construction, while
the reconstruction is proved in HCR by Lagrange interpolation and the
monogenic trace-dual formula. The classical codifferent input is explained
in A. V. Sutherland, MIT 18.785 Lecture 12 (2021), Definition 12.2,
Proposition 12.6 and the monogenic different formula:
https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf

For c in B=Q(zeta_(p^k)+zeta_(p^k)^(-1)), HCR gives the exact reciprocal
numerator N_c(Z)=Z^(d-1)R_c(Z+Z^(-1)), with
R_c(t)=c*Psi_(p^k)'(t), and denominator Phi_(p^k)(Z). The first d
prime-power coefficients determine the full form within this packet and
are integral exactly when c belongs to the codifferent. The displayed
integer inverse, odd periodic completion and its sharp maximum-norm bound
are repository derivations, not statements attributed to Tanaka.

For a non-generator rotation of order p^s, all its power observations
factor through Tr_(B/B_s). The codifferent trace is surjective onto the
smaller codifferent, and the exact kernel dimension is d-d_s. HCR treats
split identity and inert primes separately. These are task-specific
observation results, not a universal Sturm bound or an effective bound for
the selected auxiliary prime. Abstract integer sequences satisfying these
relations do not construct a global golden character.

HCR.6 consumes the existing integer-image theorem through the identity
D_j=P_j-P_(j-2), giving the ordinary-trace-lattice condition
y_j=(j+1)y_0 modulo p at the first layer. Its Scribe explanation is updated;
the Lean statement and its formula are unchanged. Neither HCR nor CTG
supplies a new actual WSS prime-family decision, and no additional kernel
certification is claimed by this literature note.

## Fixed-golden spectral derivations

The following arguments concern the [WSS golden-unit lift problem](../../Problems/wall-sun-sun-golden-unit-lift.md). They are repository derivations using the source roles distinguished below, rather than additional claims attributed to Tanaka. Their character-existence, normalization and nonvanishing conditions remain explicit.

<a id="wss-ths"></a>

### THS. Exact theta sieving and the principal-orbit coefficient

#### THS.1 The integer Fourier condition

**Definition.** Put phi=(1+sqrt(5))/2, O=Z[phi], and retain the original Fibonacci and Lucas numbers. For z=x+iy with y>0, define

$$
\Theta(z)=\sum_{n\in\mathbb Z}e^{2\pi i n^2z},\qquad
V_d(z)=\sqrt y\,\Theta(5d^2z)\overline{\Theta(z)}\quad(d\ge1),
$$

$$
C_d(b;y)=\int_0^1\Theta(5d^2z)\overline{\Theta(z)}e^{-2\pi i b x}\,dx
\quad(b=4,-4).
$$

**Theorem THS1.** For every positive integer d,

$$
C_d(b;y)=\sum_{5d^2u^2-v^2=b}e^{-2\pi y(5d^2u^2+v^2)},
$$

$$
C_d(4;y)=4e^{8\pi y}\sum_{\substack{n\ge1\text{ odd}\\d\mid F_n}}
 e^{-20\pi yF_n^2},
$$

$$
C_d(-4;y)=2e^{-8\pi y}+4e^{-8\pi y}
 \sum_{\substack{n\ge2\text{ even}\\d\mid F_n}}e^{-20\pi yF_n^2}.
\tag{THS1}
$$

**Proof.** Gaussian decay gives absolute uniform convergence on each compact horizontal segment. Termwise integration retains exactly the pairs with 5d^2u^2-v^2=b. For w=d|u|>0 and |v|>0, the equation v^2-5w^2=+/-4 implies that (|v|+w sqrt(5))/2 is a positive golden unit greater than one. Its two coordinates have the same parity, so it belongs to O. The classification O^*={+/-phi^n:n in Z} gives (|v|,w)=(L_n,F_n). The norm selects even n for +4 and odd n for -4. Each positive solution has four sign choices. When b=-4 there are additionally u=0,v=+/-2; their combined weight is 2e^(-8pi y). There are no other zero-coordinate solutions. Substituting v^2=5w^2-b gives the exponential factors shown. The two indices with F_1=F_2=1 belong to different norm equations and are counted separately.

The Pell-to-theta mechanism is classical and is used by E. Assaf, C. I. Kuan, D. Lowry-Duda and A. Walker, *The Fibonacci Zeta Function and Modular Forms*, arXiv:2502.01415v1, Proposition 2 and Section 3. THS1 retains an additional exact divisibility condition on the integer coordinate; no congruence approximation to the Pell equation is used.

#### THS.2 All square-conductor levels and inert Hecke operators

**Definition.** Let chi_5 denote the quadratic character of conductor five. The standard theta transformation law makes V_d a weight-zero automorphic function of level 20d^2 and character chi_5 induced to that level. It has moderate growth; membership in L^2 is not assumed. At a prime ell not dividing 10d, use the good Hecke normalization

$$
(T_\ell f)(z)=\ell^{-1/2}\left[
\chi_5(\ell)f(\ell z)+\sum_{j=0}^{\ell-1}f((z+j)/\ell)\right].
$$

**Theorem THS2.** If chi_5(ell)=-1, then T_ell V_d=0. Consequently V_p-V_(p^2), viewed at common level 20p^4, is killed by every such good inert operator with ell not dividing 10p.

**Proof.** Expanding the translation sum introduces

$$
\sum_{j=0}^{\ell-1}e^{2\pi i j(5d^2u^2-v^2)/\ell}.
$$

It equals ell or zero, according as 5d^2u^2-v^2 is zero or nonzero modulo ell. Inertness and ell not dividing d force both u and v to be multiples of ell in the first case. Replacing them by ell*u_0,ell*v_0 turns the surviving exponential into its value at ell*z; the scalar factor is ell*sqrt(y/ell)=sqrt(ell*y). Thus the translation sum is V_d(ell*z), and chi_5(ell)=-1 gives cancellation. Gaussian convergence justifies the interchanges. This proof uses no squarefreeness of 5d^2. The last statement follows by linearity.

**Corollary THS3.** If a simultaneous good-Hecke Maass cusp eigenform g has a nonzero Petersson pairing with V_d, its cuspidal representation satisfies

$$\pi_g\simeq\pi_g\otimes\chi_5.$$

It is therefore dihedral. The same conclusion holds for a nonzero cusp pairing with V_p-V_(p^2).

**Proof.** The cusp decay of g and moderate growth of V_d make the pairing convergent. Hecke adjointness, with the nonzero character scalar included, and THS2 force g's eigenvalue at every good inert ell to vanish. At a good split prime twisting leaves its eigenvalue unchanged; at an inert prime the zero eigenvalue is also unchanged. The local determinant is multiplied by chi_5(ell)^2=1. Strong multiplicity one gives the self-twist, and the classical quadratic-self-twist characterization gives the dihedral conclusion. Both inputs are stated in N. Walji, *Further refinement of strong multiplicity one for GL(2)*, arXiv:1308.1469. This argument concerns cuspidal projections, including oldvectors, and does not assert disappearance of all continuous or residual terms in a regularized expansion.

#### THS.3 The heat coefficient with a uniform error

**Definition.** For p>5 set r=rho(p), R=rho(p^2), where rho denotes the least positive Fibonacci zero index. Define

$$
K_p(t)=\sum_{\substack{n\ge1\\p\parallel F_n}}e^{-tF_n^2},\qquad
S_a(t)=\sum_{k\ge1}e^{-tF_{ak}^2}\quad(t>0).
$$

**Theorem THS4.** The exact Fourier difference

$$
\tfrac14\left[e^{-8\pi y}(C_p(4;y)-C_{p^2}(4;y))
 +e^{8\pi y}(C_p(-4;y)-C_{p^2}(-4;y))\right]
$$

is K_p(20pi*y). Moreover K_p(t)=S_r(t)-S_R(t), and for every a>=3 and 0<t<=1,

$$\left|S_a(t)-\frac{\log(1/t)}{2a\log\phi}\right|\le2,$$

$$\boxed{\left|K_p(t)-\kappa_p\log(1/t)\right|\le4,\qquad
\kappa_p=\frac{1/r-1/R}{2\log\phi}.}\tag{THS4}$$

**Proof.** Subtract THS1 at d=p and d=p^2; the zero-coordinate terms cancel. The zero indices modulo each positive modulus are precisely the multiples of its least zero index, by strong Fibonacci divisibility. This proves the two exact identities.

For the estimate, phi^(n-2)<=F_n<=phi^(n-1) for n>=2. Put Q=phi^(2a) and A(v,Q)=sum_(k>=1)exp(-vQ^k). Then

$$A(t\phi^{-2},Q)\le S_a(t)\le A(t\phi^{-4},Q).$$

For the decreasing function x mapping to exp(-vQ^x), the integral test gives

$$E_1(v)/\log Q-1\le A(v,Q)\le E_1(v)/\log Q,\qquad
E_1(v)=\int_v^\infty e^{-u}\,du/u.$$

For 0<v<=1, splitting the integral at one gives |E_1(v)+log v|<=1: the integral of (e^(-u)-1)/u from v to one lies in [-1,0], and the remaining tail lies in [0,e^(-1)]. With L=log(phi)>1/3, the resulting upper error is at most (4L+1)/(2aL)<2 and the lower error is at least -1-1/(2aL)>-2. This proves the uniform constant two; subtracting the two estimates proves the constant four.

**Corollary.** With the actual initial depth h_p=v_p(F_r), one has

$$
\kappa_p=0\text{ and }K_p\equiv0\quad(h_p\ge2),\qquad
\kappa_p=\frac{1-1/p}{2r\log\phi}>0\quad(h_p=1).
$$

**Proof.** The classical valuation theorem gives R=r in the first case and R=pr in the second. In the first case the exact difference of S-series is zero; in the second case n=r itself supplies a positive term. This uses Lengyel's valuation theorem as recorded in Medina-Rowland, *p-regularity of the p-adic valuation of the Fibonacci sequence*, Fibonacci Quarterly 53 (2015), Theorem 1.4, arXiv:0910.2907. No branch is chosen in THS4 without this actual arithmetic input.

#### THS.4 The pole and the local density

**Theorem THS5.** For a>=3, the series Z_a(s)=sum_(k>=1)F_(ak)^(-s), initially on Re(s)>0, has the representation

$$Z_a(s)=\frac{5^{s/2}}{\phi^{as}-1}+H_a(s),$$

where H_a is holomorphic on Re(s)>-2 and H_a(0)=0. Thus D_p(s)=Z_r(s)-Z_R(s) satisfies

$$\operatorname{Res}_{s=0}D_p(s)=\frac{1/r-1/R}{\log\phi},\qquad
\int_0^\infty K_p(t)t^{s-1}\,dt=\Gamma(s)D_p(2s)\quad(\Re s>0).$$

**Proof.** Use F_(ak)=5^(-1/2)phi^(ak)(1-(-1)^(ak)phi^(-2ak)). The last factor is positive. After subtracting its leading value one, the summands are normally bounded on a compact subset of Re(s)>-2 by a constant times phi^(-ak(Re(s)+2)). This proves normal convergence and holomorphy of H_a; each remainder vanishes at s=0. The residue follows from the geometric term. Absolute convergence justifies Mellin integration term by term. Other geometric poles on the imaginary axis are not excluded by this representation.

**Theorem THS6.** For every p>5 and k>=2, the number of pairs (v,w) modulo p^k with

$$v^2-5w^2=4,\qquad p\mid w,\quad p^2\nmid w$$

is 2(p-1)p^(k-2). Replacing four by minus four gives the same count when p=1 modulo four and zero otherwise.

**Proof.** There are (p-1)p^(k-2) choices for w. In the first equation v has the two simple roots +2,-2 modulo p; each uniquely lifts for each w by Hensel's lemma. For minus four, the two roots exist precisely when -1 is a square modulo p, and are again simple. These are local solutions; the count does not assert that any chosen solution is a reduction of a global pair (L_n,F_n) in the simple-divisor window.


<a id="wss-roc"></a>

### ROC. Fixed-golden orders, mixed-conductor kernels, and zero-parameter dihedral forms

#### ROC.1 The ordinary order class group and the unit image

**Definition.** Fix K=Q(sqrt(5)), O=Z[phi]. For a positive integer f coprime to ten define

$$O_f=\mathbb Z+fO,\qquad P_f=\operatorname{Pic}(O_f),\qquad H(f)=|P_f|,$$

$$C_f=(O/fO)^\times/(\mathbb Z/f\mathbb Z)^\times,\qquad
r(f)=\min\{n\ge1:f\mid F_n\},\quad r(1)=1.$$

P_f is the ordinary group of invertible ideal classes, with no positivity restriction on principal ideals. It is not the narrow class group. The field K remains fixed as f varies. At f=1 all finite quotient groups in the formulas are trivial.

**Theorem ROC1.** There is a natural isomorphism

$$\boxed{P_f\simeq C_f/\langle[\phi]\rangle,\qquad
\operatorname{ord}_{C_f}([\phi])=r(f).}\tag{ROC1}$$

If f and g are coprime, r(fg)=lcm(r(f),r(g)).

**Proof.** The classical exact sequence for an order and its conductor is

$$O^\times\longrightarrow (O/fO)^\times/(O_f/fO)^\times
\longrightarrow\operatorname{Pic}(O_f)\longrightarrow\operatorname{Pic}(O)
\longrightarrow1.$$

Here O_f/fO=Z/fZ. The golden ring is norm-Euclidean, hence Pic(O)=1. For example rounding the two coefficients in the basis (1,phi) leaves norm of absolute value at most 5/16, which proves Euclidean division. Its unit group is {+/-phi^n:n in Z}. One proof normalizes a positive real unit into [1,phi); a strictly interior value would have an integral trace strictly between zero and one for norm -1, or between two and sqrt(5) for norm +1. Thus the normalized unit is one. The sign -1 is already scalar in C_f, so the unit image is generated by [phi].

The coordinate identity phi^n=F_(n-1)+F_n*phi makes its class scalar precisely when f|F_n. If scalar, it is a scalar unit because phi^n is a unit and O/fO is free over Z/fZ. Thus its order is r(f). Existence follows from finiteness of C_f. For coprime f,g, divisibility by fg is simultaneous divisibility by f and g; equivalently the two cyclic components must return at the same exponent. This gives the least common multiple.

The order exact sequence and its class-field interpretation are classical inputs: C. Lv and Y. Deng, *On Orders in Number Fields: Picard Groups, Ring Class Fields and Applications*, Sci. China Math. 58 (2015), 1627-1638, Proposition 2.3(e), Theorems 3.11 and 4.2, DOI 10.1007/s11425-015-4979-3, arXiv:1405.5776.

#### ROC.2 The complete prime-power conductor tower

**Theorem ROC2.** For p>5, a>=1, and chi_p=(5/p), the group C_(p^a) is cyclic of order (p-chi_p)p^(a-1). With the actual h_p and

$$M_p=(p-\chi_p)/r(p),$$

one has p not dividing M_p and

$$\boxed{P_{p^a}\simeq
\mathbb Z/\bigl(M_p p^{\min(a-1,h_p-1)}\bigr)\mathbb Z.}\tag{ROC2}$$

The extension-of-ideals map P_(p^(a+1))->P_(p^a) is surjective, and its kernel has order p when a<h_p and order one when a>=h_p. In particular

$$\boxed{q_p=0\iff\ker(P_{p^2}\longrightarrow P_p)\ne1.}\tag{ROC3}$$

**Proof.** In the split case O tensor Z_p=Z_p x Z_p, and division by scalar units identifies the quotient with (Z/p^aZ)^*. In the inert case the Teichmueller-unit quotient is cyclic of order p+1. The principal-unit logarithm identifies the remaining quotient with

$$pO_p/(p\mathbb Z_p+p^aO_p),$$

a cyclic group of order p^(a-1). The two factors have coprime orders, so their product is cyclic. Reduction from a+1 to a is surjective with a cyclic order-p kernel.

The classical Fibonacci valuation formula gives r(p^a)=r(p)p^max(a-h_p,0). Indeed any zero index is r(p) times an integer j, and its valuation is h_p+v_p(j); r(p) divides p-chi_p and is prime to p. Dividing the order of C_(p^a) by this unit-image order proves ROC2. This use of the full valuation formula retains h_p, as in Medina-Rowland, Theorem 1.4. Quotient reduction stays surjective since the same generator phi maps to phi. Taking the ratio of the displayed orders proves the kernel assertions and ROC3.

**Corollary.** The p-primary parts of P_(p^a) stabilize to a cyclic group of order p^(h_p-1). This assertion concerns the nonmaximal orders O_(p^a) in K; it makes no claim about the full class group of the different field K(zeta_p).

**Proof.** The prime-to-p factor is M_p, and min(a-1,h_p-1) becomes constant at a=h_p.

#### ROC.3 The mixed-conductor kernel

**Theorem ROC4.** For coprime f,g, both coprime to ten, there is a natural exact sequence

$$\boxed{
1\longrightarrow\mathbb Z/\gcd(r(f),r(g))\mathbb Z
\longrightarrow P_{fg}\longrightarrow P_f\times P_g\longrightarrow1.
}\tag{ROC4}$$

In particular H(fg)=H(f)H(g)gcd(r(f),r(g)).

**Proof.** CRT gives C_(fg)=C_f x C_g. The subgroup generated by the global unit is diagonal: it consists of ([phi]^n,[phi]^n) with a single integer n. Therefore the map to the two separate quotients is surjective and its kernel is

$$(\langle\phi_f\rangle\times\langle\phi_g\rangle)/
\langle(\phi_f,\phi_g)\rangle.$$

On the numerator, send (phi_f^u,phi_g^v) to u-v modulo gcd(r(f),r(g)). This is well-defined and surjective. Its kernel consists precisely of pairs for which the simultaneous congruences n=u modulo r(f), n=v modulo r(g) are soluble, hence is the diagonal subgroup. This proves the group statement, including trivial ranks, and counting proves the formula.

**Theorem ROC5.** Fix p>5 and m coprime to 10p. Put b=v_p(r(m)). For every a>=1,

$$\boxed{
\left|\ker(P_{mp^{a+1}}\longrightarrow P_{mp^a})\right|
=\begin{cases}p,&a<h_p+b,\\1,&a\ge h_p+b.\end{cases}
}\tag{ROC5}$$

Every nontrivial kernel here is cyclic.

**Proof.** The ambient C-group has a cyclic order-p reduction kernel. The p-exponent of the image of the global unit at level mp^a is

$$\max\{b,\max(a-h_p,0)\},$$

because its order is lcm(r(m),r(p)p^max(a-h_p,0)) and p does not divide r(p). The unit-image size increases by p at the next level exactly when a>=h_p+b; all its other prime-exponents remain unchanged. The Picard-group size ratio is consequently one in that case and p otherwise. The Picard kernel is a quotient of the ambient cyclic reduction kernel: any element mapping into the lower unit image can be multiplied by a lifted power of phi to enter that reduction kernel. This proves cyclicity as well as its exact size.

**Proposition ROC6.** The increase H(mp^2)>H(mp) at a mixed conductor does not imply p is WSS. In fact

$$r(7)=8,\quad h_7=1,\quad r(13)=7,\quad H(91)=2,\quad H(637)=14.$$

**Proof.** F_8=21 and F_1=1,F_2=1,F_4=3 show r(7)=8 and h_7=1. F_7=13 and the prime-index argument show r(13)=7. For coprime prime powers ROC1-ROC2 give

$$H(91)=\frac{8\cdot14}{\operatorname{lcm}(8,7)}=2,\qquad
H(637)=\frac{56\cdot14}{\operatorname{lcm}(56,7)}=14.$$

The order-seven kernel is caused by v_7(r(13))=1 in ROC5, although seven is non-WSS. Thus the correction b cannot be omitted when inferring initial depths from mixed-conductor growth.

#### ROC.4 Finite-order characters and exact conductor

**Definition.** An ordinary ring-class character of conductor dividing f is a character of P_f, inflated along the natural maps for larger conductors. Its least rational conductor is the smallest positive f through which it factors. Through classical ring class field theory it defines a finite Hecke character of K trivial at both real places and on rational ideles. For k>=1 let X_(p,k) be the set of such characters of exact order p^k whose conductor is a power of p, identifying repeated inflations of the same character.

**Theorem ROC7.** For all p>5 and k>=1,

$$\boxed{|X_{p,k}|=
\begin{cases}p^{k-1}(p-1),&h_p\ge k+1,\\0,&h_p<k+1.\end{cases}}\tag{ROC7}$$

When present, every character in X_(p,k) has least rational conductor p^(k+1) and Hecke conductor ideal p^(k+1)O. It satisfies eta^sigma=eta^(-1), where sigma is golden conjugation.

**Proof.** By ROC2 the p-primary part of P_(p^a) is cyclic of order p^min(a-1,h_p-1), and all transition maps are surjective. A character of exact order p^k exists exactly when h_p>=k+1 and a>=k+1. At a=k+1 its number is the Euler totient p^(k-1)(p-1). At every later level all characters of that order factor uniquely through this quotient, since a cyclic p-group has a unique subgroup of each order. The prime-to-p factor contributes no nontrivial values to a p-power-order character. This proves both the count and least rational conductor.

Conjugation acts by inversion on C_f, since x*sigma(x) is a scalar unit, and hence on P_f. The attached Hecke characters are therefore anticyclotomic. Their finite conductors are supported above p. If p splits, the two local conductor exponents are equal because the conjugate character is the inverse; if p is inert there is one exponent. Triviality on local scalar units and on global units shows that such a character has conductor dividing p^aO precisely when it factors through P_(p^a). Its least a is k+1, proving the stated ideal conductor in both cases. The ordinary class-group convention permits all real units at infinity, so the real components are trivial. Rational ideles are generated by rational principal ideles, the real factor, and scalar finite units; the character is trivial on each. The class-field interpretation is the one in Lv-Deng, Theorem 4.2.

#### ROC.5 A precisely specified spectral family at eigenvalue one quarter

**Definition.** Let D_(p,k) be the set of cuspidal GL(2)/Q representations obtained by automorphic induction from X_(p,k), up to isomorphism. Only this fixed-K, finite p-power-order, ordinary ring-class family is included in D_(p,k).

**Theorem ROC8.** Every representation in D_(p,k) has weight zero, Laplace eigenvalue 1/4, central character chi_5, and exact arithmetic conductor 5p^(2k+2). Moreover

$$\boxed{|D_{p,k}|=
\frac{p^{k-1}(p-1)}2\,\mathbf1_{h_p\ge k+1}.}\tag{ROC8}$$

In particular p is WSS if and only if D_(p,1) is nonempty, in which case its size is (p-1)/2 and its exact conductor is 5p^4.

**Proof.** Classical Hecke-Maass automorphic induction attaches a normalized eigenform to eta, and is cuspidal when eta is not equal to eta^sigma. Here eta^sigma=eta^(-1) and eta has odd order greater than one, so cuspidality holds. The induced two-dimensional finite-image representation sends complex conjugation to the identity, because K is real and both real components of eta are trivial. Its Maass eigenvalue is therefore 1/4. The central character is chi_5 times the restriction of eta to rational ideles, hence is chi_5. These classical finite-order induction statements, including the eigenvalue, are stated in W.-C. W. Li and Z. Rudnick, *Pair arithmetical equivalence for quadratic fields*, arXiv:2007.13147v2, Section 1.3.

The conductor-discriminant formula for automorphic induction gives the exact conductor |disc(K)|*N_(K/Q)(cond eta)=5p^(2k+2). See P. Humphries, *Archimedean Newform Theory for GL_n*, Theorem 3.12 and Remark 3.13, DOI 10.1017/S1474748024000227. For the same quadratic field, two induced irreducible representations are isomorphic precisely when their inducing characters agree or are conjugate: restrict the induced representation back to K to get eta plus eta^sigma. Thus the fixed-point-free pairing eta with eta^(-1) accounts for the factor two in ROC8.

An explicit normalization of the corresponding even Maass form is

$$
g_\eta(x+iy)=2\sqrt y\sum_{\substack{\mathfrak a\subset O\\
(\mathfrak a,p)=1}}\eta(\mathfrak a)
 K_0(2\pi N\mathfrak a\,y)\cos(2\pi N\mathfrak a\,x).
$$

The term of norm one has coefficient one in the normalized exponential Fourier expansion, so the constructed form is not zero. The sum converges for y>0 by the exponential decay of K_0. This is the classical Fourier construction in Li-Rudnick, Section 1.3, applied after the ring-class characters have been obtained. It does not establish their existence without the condition in ROC7.

**Corollary.** Forms in D_(p,1), when they exist, can be viewed as oldforms at the theta-sieve level 20p^4. ROC8 does not count all cusp forms, all dihedral forms from other quadratic fields, or forms induced from characters with nontrivial archimedean parameter.

**Proof.** Their exact conductor 5p^4 divides 20p^4, so oldform inclusion applies. The exclusions follow from the defining restrictions on D_(p,k); no assertion about other spectral components is used in the count.

#### ROC.6 The class-growth coefficient and the remaining independent condition

**Theorem ROC9.** The coefficient in THS4 has the exact expression

$$\boxed{\kappa_p=
\frac{pH(p)-H(p^2)}{2p(p-\chi_p)\log\phi}.}\tag{ROC9}$$

The family D_(p,1) is nonempty exactly in the branch where K_p is identically zero. Nonemptiness of this family therefore does not imply nonvanishing of the particular Fourier difference in THS4.

**Proof.** ROC1-ROC2 give H(p)=(p-chi_p)/r and H(p^2)=p(p-chi_p)/R. Substitute in THS4. ROC3 and ROC8 identify nonemptiness with h_p>=2; the exact S-series difference in THS4 is then zero. This does not assert that each individual spectral projection of V_p-V_(p^2) vanishes: contributions to a selected Fourier functional may cancel, and a nonzero representation need not occur in that theta projection at all.

**Proposition.** The identities THS1-THS6 and ROC1-ROC9 leave the actual set of primes with h_p>=2 undetermined. In particular, a vanishing theorem for D_(p,1) on a specified prime family would exclude WSS in that family, while an independently constructed member would give a WSS prime; neither existence nor vanishing on a new family follows from the displayed counts alone.

**Proof.** ROC8 expresses the count in terms of the same actual h_p, and ROC9 expresses the heat coefficient in terms of its unit-image size. No inequality choosing a branch is among the hypotheses or conclusions used to prove those identities. The logical implications in the proposition follow directly from ROC8, but their antecedents require information additional to the formula. The fixed eigenvalue is 1/4 at every conductor, so estimates that only treat growing archimedean spectral parameter do not by themselves supply either antecedent.


<a id="wss-sgn"></a>

### SGN. Spectral Galois arithmetic, exact congruence ideals, and packet norms

#### SGN.1 Fixed fields and Fourier normalization

**Definition.** Retain the fixed golden field K=Q(sqrt(5)), O=Z[phi], the original depth h_p, and the ordinary ring-class families X_(p,k), D_(p,k) of ROC. For this section take p>5, k>=1, and assume h_p>=k+1. Choose eta in X_(p,k), put m=p^k, d_k=p^(k-1)(p-1)/2, and N_k=5p^(2k+2). Let L_(p,k)/K be the cyclic class-field extension cut out by eta. All primitive characters of this cyclic quotient have the same kernel. Write sigma for golden conjugation.

The extension L_(p,k)/Q is totally real and dihedral of degree 2m. Indeed its kernel is stable under sigma, which acts by inversion on its cyclic group. A lift s of sigma satisfies s^2=tau^j for a rotation tau. Commutation of s with s^2 and inversion of rotations imply 2j=0 modulo the odd number m, so s^2=1. Let M_(p,k) be the fixed field of a chosen reflection. It is totally real of degree m. Choose the reflections compatibly in the tower, and put M_(p,0)=Q. These fields are different from the radical fields E_n of RNI and the coefficient fields below.

Define the integral ideal coefficients, with eta extended by zero on ideals not coprime to p, by

$$
A_\eta(n)=\sum_{N\mathfrak a=n}\eta(\mathfrak a),\qquad
 g_\eta(z)=\sqrt y\sum_{n\ne0}A_\eta(|n|)K_0(2\pi|n|y)e^{2\pi inx}.
\tag{SGN1}
$$

Thus A_eta(1)=1 and this g_eta is the form normalized in ROC8. Its Petersson norm at the minimal level is the unscaled integral with measure dx dy/y^2 over Gamma_0(N_k)\H. Daichi Tanaka, *Explicit Construction of Maass Wave Forms and Their Petersson Inner Products*, arXiv:2601.21588v3 (February 3, 2026), Theorem 1.1, uses the cosine sum Theta_eta=g_eta/2. The construction theorem is classical input; all norm constants below are derived with the normalization in SGN1.

#### SGN.2 The exact coefficient field and its first congruence ideal

**Theorem SGN2.** Choose a primitive mth root of unity zeta, identify the image of eta with its powers, and put

$$B_m=\mathbb Q(\zeta+\zeta^{-1}),\qquad
\lambda_m=2-\zeta-\zeta^{-1},\qquad\mathfrak l_m=(\lambda_m)\subset O_{B_m}.$$

Every A_eta(n) is integral and belongs to B_m. The field generated by the good-prime coefficients is exactly B_m, of degree d_k. The d_k forms g_(eta^j), with j in (Z/mZ)^*/{+1,-1}, form one coefficientwise Galois orbit. Moreover l_m is the unique prime of B_m above p, its norm is p, and pO_(B_m)=l_m^(d_k).

**Proof.** Conjugation of ideals pairs eta(a) with eta(a)^(-1). A fixed ideal coprime to p under sigma has character value equal to its inverse, hence one because its order is odd. Thus the ideal sum is real and integral in Q(zeta). For a good rational prime ell not dividing 5p, if ell is inert the coefficient is zero. If ell splits as q*sigma(q), then

$$A_\eta(\ell)=\zeta^b+\zeta^{-b},\qquad \eta(\mathfrak q)=\zeta^b.$$

Chebotarev applied to the already-defined L_(p,k)/Q supplies primes with Frobenius the conjugacy class of a generator rotation. For one such ell the coefficient is zeta+zeta^(-1), proving equality of coefficient fields. The action zeta mapping to zeta^j gives the stated Galois orbit; equality of two induced forms forces the characters to agree or be inverse, as in ROC8.

The shifted polynomial Phi_(p^k)(1+X) is Eisenstein at p. Hence p is totally ramified in Q(zeta), with uniformizer 1-zeta and norm p. Since lambda_m=(1-zeta)(1-zeta^(-1)), its valuation in that cyclotomic field is two. Passing to the real subfield divides the valuation by two; its absolute norm there is p, using Phi_(p^k)(1)=p. Total ramification and the displayed degree give the ideal assertions. Chebotarev is used only after the extension exists; see A. V. Sutherland, MIT 18.785 Lecture 28 (2021), Theorem 28.9. It is not an existence theorem for the missing ring-class character at an arbitrary target p.

**Theorem SGN3.** Put b(n)=sum_(a|n)chi_5(a). Then for (n,5p)=1,

$$A_\eta(n)\equiv b(n)\pmod{\mathfrak l_m}.$$

The ideal generated by all good-prime discrepancies is exactly

$$\boxed{\bigl(A_\eta(\ell)-1-\chi_5(\ell):\ell\nmid5p\bigr)
=\mathfrak l_m.}\tag{SGN2}$$

For a split good prime, write eta(q)=zeta^b. If b is nonzero modulo p^k and j=v_p(b)<k, then

$$\boxed{v_{\mathfrak l_m}(A_\eta(\ell)-2)=p^j,\qquad
\bigl|N_{B_m/\mathbb Q}(A_\eta(\ell)-2)\bigr|=p^{p^j}.}\tag{SGN3}$$

When p does not divide b, one additionally has

$$\boxed{\frac{A_\eta(\ell)-2}{\lambda_m}\equiv-b^2\pmod{\mathfrak l_m}.}\tag{SGN4}$$

**Proof.** Reduction of every root of unity eta(a) modulo 1-zeta gives one. The number of ideals of norm n in K is sum_(a|n)chi_5(a); pairing with the real subfield gives the first congruence. At an inert good prime the discrepancy is zero. At a split prime,

$$A_\eta(\ell)-2=(\zeta^b-1)^2/\zeta^b.$$

The cyclotomic valuation of 1-zeta^b is p^j: zeta^b is a primitive p^(k-j)th root, whose cyclotomic subfield has ramification index smaller by p^j. Its ideal has no support outside p. Squaring and passing to B_m proves both assertions in SGN3. For p not dividing b the ratio (1-zeta^b)/(1-zeta) reduces to b. Since lambda_m=-(zeta-1)^2/zeta, the quotient in SGN4 reduces to -b^2. Every discrepancy therefore belongs to l_m, while a generator Frobenius from SGN2 gives the exact discrepancy -lambda_m. This proves the ideal equality, including the fact that no larger common power of l_m is forced.

**Corollary SGN4.** As the auxiliary good rational prime ell varies, the set on which the discrepancy in SGN2 has finite l_m-valuation p^j has Dirichlet density

$$\frac{p-1}{2p^{j+1}}\quad(0\le j<k).$$

The set on which that discrepancy is zero has density 1/2+1/(2p^k).

**Proof.** In the dihedral group of order 2p^k there are (p-1)p^(k-j-1) rotations with exponent of p-valuation j. The union is stable under conjugation, so Chebotarev gives its size divided by 2p^k. All reflections and the identity rotation give zero discrepancy, with combined size p^k+1. These densities concern auxiliary primes in one existing number field. They are not a density theorem for WSS as the target p varies.

#### SGN.3 An explicit residual lattice

**Theorem SGN5.** Let t=zeta+zeta^(-1). The matrices

$$R=\begin{pmatrix}0&-1\\1&t\end{pmatrix},\qquad
S=\begin{pmatrix}0&1\\1&0\end{pmatrix}$$

give an integral realization over O_(B_m) of the dihedral representation attached to eta: R^m=I, S^2=I, SRS=R^(-1). After reduction modulo l_m and pullback along Gal(L_(p,k)/Q), the associated Galois representation has a nonsplit exact sequence

$$\boxed{0\longrightarrow\mathbb F_p(\chi_5)
\longrightarrow\overline\rho_\eta\longrightarrow\mathbb F_p
\longrightarrow0.}\tag{SGN5}$$

Its semisimplification is 1 plus chi_5, and complex conjugation acts as the identity.

**Proof.** R has distinct eigenvalues zeta,zeta^(-1) in the cyclotomic field and therefore order m. Direct multiplication proves the two relations involving S. Modulo l_m one has t=2, R not equal to I, and (R-I)^2=0. Its fixed space is the line generated by (1,-1); S acts by minus one on that line and by plus one on the quotient. This identifies the two characters. A direct sum of those characters would make every rotation act trivially, whereas the displayed residual R is nontrivial unipotent. Thus the sequence does not split. The totally real field L_(p,k) makes complex conjugation trivial. For k>1 the residual rotation has order p, although the characteristic-zero rotation has order p^k. This does not retain all higher order in the residual image.

The congruence is an Eisenstein-type coefficient congruence, but the representation is even. No theorem whose hypotheses require an odd holomorphic two-dimensional Galois representation is invoked by SGN5.

#### SGN.4 A normalized Rankin-Selberg calculation at spectral parameter zero

**Lemma SGN6.** For Re(s)>0, with the standard modified Bessel function K_0,

$$\boxed{\int_0^\infty y^{s-1}K_0(y)^2\,dy
=2^{s-3}\frac{\Gamma(s/2)^4}{\Gamma(s)}.}\tag{SGN6}$$

In particular the value at s=1 is pi^2/4.

**Proof.** Schlaefli's representation is

$$K_0(y)=\tfrac12\int_0^\infty e^{-u-y^2/(4u)}\,du/u,$$

as in NIST DLMF 10.32.10. For real s>0, Tonelli's theorem applies to the square. The y-integral is Gamma(s/2)/2 times (4uv/(u+v))^(s/2). The remaining double integral is

$$2^{s-3}\Gamma(s/2)\int_0^\infty\int_0^\infty
 e^{-u-v}u^{s/2-1}v^{s/2-1}(u+v)^{-s/2}\,du\,dv.$$

Set w=u+v and x=u/(u+v). The w-integral is Gamma(s/2) and the x-integral is Beta(s/2,s/2). This gives SGN6. Absolute convergence on Re(s)>0 and holomorphic continuation within that half-plane prove the complex statement.

**Theorem SGN7.** With N=N_k and the exact Fourier normalization SGN1,

$$\boxed{\langle g_\eta,g_\eta\rangle_N
=\frac N2\left(1-\frac{\chi_5(p)}p\right)
 L(1,\chi_5)L_K(1,\eta^2).}\tag{SGN7}$$

All Euler factors at five and p are included in this formula.

**Proof.** The coefficients A_eta(n) are real. Put D_eta(s)=sum_(n>=1)A_eta(n)^2 n^(-s). The ideal Euler factors give

$$D_\eta(s)=\frac{\zeta(s)L(s,\chi_5)L_K(s,\eta^2)}{\zeta(2s)}
\frac1{1+5^{-s}}\frac{1-\chi_5(p)p^{-s}}{1+p^{-s}}.\tag{SGN8}$$

To check this at every prime, write x=ell^(-s). At a good split prime with eta(q)=z, the squared-coefficient series is

$$\frac{1+x}{(1-x)(1-z^2x)(1-z^{-2}x)}.$$

This follows by squaring sum_(j=0)^a z^(a-2j) and summing geometric series; as a rational identity it includes z=+1,-1 by continuation. At a good inert prime it is (1-x^2)^(-1). At the prime five, its unique prime ideal q has q^2=(5), so eta(q)=1 because eta has odd order and is trivial on rational ideles. The squared-coefficient factor is (1-5^(-s))^(-1), producing the factor (1+5^(-s))^(-1) in SGN8. At p, eta and eta^2 are ramified at every prime above p, so the ideal series has local factor one. Comparison with zeta(s)L(s,chi_5)/zeta(2s) gives the final correction in SGN8.

Let E_infinity(z,s) be the standard weight-zero Eisenstein series for Gamma_0(N), with the stabilizer including both signs. Its residue at s=1 is 1/vol=3/(pi*i_N), where i_N=N product_(ell|N)(1+1/ell). Unfolding and SGN6 give

$$\int_{\Gamma_0(N)\backslash\mathbb H}
 E_\infty(z,s)|g_\eta(z)|^2\,\frac{dx\,dy}{y^2}
=\frac{\Gamma(s/2)^4}{4\pi^s\Gamma(s)}D_\eta(s).\tag{SGN9}$$

The scalar at s=1 is pi/4. Taking residues and using zeta(2)=pi^2/6, the factor 5/6 from the prime five, and the factor (1-chi_5(p)/p)/(1+1/p), cancels i_N down to the right side of SGN7. All unfolding operations first take place on Re(s)>1; cusp decay permits the residue passage. The standard Eisenstein residue and this Rankin-Selberg normalization are also recorded in P. Humphries and R. Khan, *On the Random Wave Conjecture for Dihedral Maass Forms*, GAFA 30 (2020), proof of Lemma 4.4 and equation (4.8), DOI 10.1007/s00039-020-00526-4. The present bad-prime factors are computed above and are not taken from a squarefree-level specialization.

**Proposition SGN8.** In the standard K_0 convention, the coefficient 2^(s-2) in Tanaka, arXiv:2601.21588v3, Lemma 4.2, must be replaced by 2^(s-3) when nu=0. For the family in SGN1 the cosine normalization Theta_eta=g_eta/2 therefore has

$$\boxed{\langle\Theta_\eta,\Theta_\eta\rangle_N
=\frac N8\left(1-\frac{\chi_5(p)}p\right)
 L(1,\chi_5)L_K(1,\eta^2).}\tag{SGN10}$$

This is half the expression obtained by specializing the printed Theorem 1.3 of that version to this family.

**Proof.** At nu=0,s=1, SGN6 gives pi^2/4, whereas the stated factor 2^(s-2) gives pi^2/2 with the same K_0 integral. The cosine definition in that paper has first exponential Fourier coefficient 1/2, so its norm is one quarter of SGN7. In its printed constants C_1 C_2 C_3, put nu=0 and conductor ideal p^(k+1)O. Then C_2=pi, the first product in C_3 is empty, and the other Euler factors cancel the totient in C_1, yielding N/4 times (1-chi_5(p)/p) times the two L-values. This differs from SGN10 by exactly two. SGN7 was derived independently from the standard Bessel integral and the width-one Eisenstein residue; the uncorrected printed norm is not a premise. This proposition concerns that normalization and specialization, not the validity of the construction theorem or all other assertions of the paper.

#### SGN.5 The Galois-packet Gram determinant and a global regulator identity

**Definition.** Let G_(p,k) be the d_k by d_k Gram matrix of the forms g_(eta^j) for j in (Z/p^kZ)^*/{+1,-1}, all at their common minimal level N_k, with no L^2 rescaling. For a totally real field M let h(M) be its ordinary ideal class number and Reg(M) its standard Dirichlet regulator; put h(Q)=Reg(Q)=1. These class numbers are not the order class numbers H(f) of ROC and are not the initial depths h_p.

**Theorem SGN9.** The Gram matrix is diagonal and

$$\boxed{\det G_{p,k}
=\left[\frac{N_k}{2}\left(1-\frac{\chi_5(p)}p\right)L(1,\chi_5)\right]^{d_k}
\frac{\operatorname{Res}_{s=1}\zeta_{M_{p,k}}(s)}
     {\operatorname{Res}_{s=1}\zeta_{M_{p,k-1}}(s)}.}\tag{SGN11}$$

In particular it has the explicit form

$$\boxed{\det G_{p,k}
=\bigl[4p^k(p-\chi_5(p))\log\phi\bigr]^{d_k}
\frac{h(M_{p,k})\operatorname{Reg}(M_{p,k})}
     {h(M_{p,k-1})\operatorname{Reg}(M_{p,k-1})}.}\tag{SGN12}$$

**Proof.** Choose a good split Frobenius generating the rotation group as in SGN2. Its Hecke operator is self-adjoint since chi_5(ell)=1. Its eigenvalues zeta^j+zeta^(-j) on the displayed primitive forms are pairwise distinct, so those forms are orthogonal.

For a dihedral group D_m, the permutation representation on cosets of a reflection is the trivial representation plus each two-dimensional irreducible representation once. The quotient field M_(p,k-1) contributes exactly the representations whose rotation characters factor through the quotient of order p^(k-1). Subtraction leaves precisely the primitive characters indexed by j above. The induction property of Artin L-functions therefore gives the identity, including ramified Euler factors,

$$\frac{\zeta_{M_{p,k}}(s)}{\zeta_{M_{p,k-1}}(s)}
=\prod_{j\in(\mathbb Z/p^k\mathbb Z)^*/\{\pm1\}}L_K(s,\eta^j).\tag{SGN13}$$

Multiplication by two permutes these classes of exponents. Multiply SGN7 over all j and then take s=1 in SGN13 to obtain SGN11.

The conductor-discriminant formula for the same permutation representation gives

$$\frac{\operatorname{disc}(M_{p,k})}{\operatorname{disc}(M_{p,k-1})}
=N_k^{d_k}.\tag{SGN14}$$

Here every remaining irreducible constituent has exact conductor N_k by ROC8; both discriminants are positive. Since [M_(p,k):Q]-[M_(p,k-1):Q]=2d_k and both fields are totally real with only two roots of unity, the analytic class number formula gives

$$\frac{\operatorname{Res}\zeta_{M_{p,k}}}{\operatorname{Res}\zeta_{M_{p,k-1}}}
=\frac{2^{2d_k}}{N_k^{d_k/2}}
\frac{h(M_{p,k})\operatorname{Reg}(M_{p,k})}
     {h(M_{p,k-1})\operatorname{Reg}(M_{p,k-1})}.$$

Finally L(1,chi_5)=2log(phi)/sqrt(5), since K has class number one and fundamental unit phi. Inserting this and sqrt(N_k)=sqrt(5)p^(k+1) into SGN11 proves SGN12. The analytic class number formula is classical; see Sutherland, MIT 18.785 Lecture 19 (2021), Theorem 19.12. The Artin induction and conductor-discriminant identities are classical class-field inputs, also used in Tanaka, Section 4.2, for low-degree dihedral examples. No regulator approximation is used in this equality.

**Corollary.** At the WSS threshold k=1, put d=(p-1)/2. The reflection field satisfies

$$\operatorname{disc}(M_{p,1})=5^{(p-1)/2}p^{2(p-1)},$$

and the normalized packet has

$$\det G_{p,1}=[4p(p-\chi_5(p))\log\phi]^d
 h(M_{p,1})\operatorname{Reg}(M_{p,1}).$$

**Proof.** Specialize SGN12-SGN14 and use M_(p,0)=Q. The fields and the packet in these formulas have been constructed under h_p>=2; the formula does not assert that such a field exists at a target prime without that hypothesis.

#### SGN.6 Exact scope of the spectral constraints

**Proposition.** SGN2-SGN12 give necessary coefficient-field, congruence, residual-representation and norm identities for each member of the finite-order family D_(p,k). None supplies an independent existence or vanishing theorem for that family at a new target prime. In particular positivity of SGN7 does not imply h_p>=k+1.

**Proof.** The field L_(p,k), its primitive character eta, and hence all forms and matrices in those theorems were defined only after choosing eta in X_(p,k). By ROC7 this is equivalent to h_p>=k+1. Chebotarev in SGN2-SGN4 describes auxiliary primes in that already-existing field, rather than creating it. The positive norm in SGN7 is the norm of an already-existing normalized cusp form; it is not a lower bound for the number of such forms. An independent construction satisfying these spectral specifications would, via ROC8, decide a WSS depth, while an independent obstruction would exclude that depth. The displayed identities do not choose either alternative. Estimates in a large archimedean-parameter limit have additional hypotheses to check here, since every form under discussion has parameter zero and varying level.


<a id="wss-stl"></a>

### STL. Saturated spectral trace lattices and exact loss under reduction

#### STL.1 Actual coefficient span and rational descent

**Definition.** Retain an existing character eta in X_(p,k) of ROC, with p>5, k>=1 and actual h_p>=k+1. Put m=p^k, d=p^(k-1)(p-1)/2, zeta=zeta_m, t=zeta+zeta^(-1), and B=Q(t). For each real embedding sigma of B let g_sigma be the SGN-normalized conjugate of g_eta. For a in B define

$$F_a=\sum_{\sigma:B\hookrightarrow\mathbb R}\sigma(a)g_\sigma.$$

Its nth coefficient is Tr_(B/Q)(a A_eta(n)). Let V_Q be the set of these forms, let L_tr={F_a:a in O_B}, and let L_int be the set of rational-coefficient forms in the real span of the g_sigma whose every Fourier coefficient is in Z. All statements below concern this already-existing finite-order family.

**Lemma STL1.** One has O_B=Z[t]. The Z-span of A_eta(n) for n=1 and good split primes is O_B. More precisely, write t_j=zeta^j+zeta^(-j). There are distinct good split primes ell_1,...,ell_(d-1) such that

$$A_\eta(\ell_j)=t_j,\qquad
(e_0,e_1,\ldots,e_{d-1})=(1,t_1,\ldots,t_{d-1})$$

is an integral basis. No effective bound for these auxiliary primes is asserted.

**Proof.** The classical cyclotomic integer theorem gives O_(Q(zeta))=Z[zeta]. Because zeta^2=t*zeta-1, every cyclotomic integer can be written U(t)+zeta*V(t), with U,V in Z[X]. If it is real, comparison with its conjugate gives (zeta-zeta^(-1))*V(t)=0, hence V(t)=0. Thus the real integers are Z[t]. The degree of t is d. The recurrence t_0=2,t_1=t,t_(j+1)=t*t_j-t_(j-1) makes t_j a monic degree-j polynomial in t for j>=1. The displayed basis is therefore a unitriangular change from the integral power basis.

For each j, Chebotarev in the existing dihedral field L_(p,k) gives a good split prime with rotation Frobenius tau^j or tau^(-j). Its coefficient is t_j. The exponents 1,...,d-1 represent distinct pairs modulo m, so the primes may be chosen distinct. Every other coefficient belongs to O_B by SGN2. This proves the full Z-span, including both containments. The integral-basis fact is classical; see J. J. Liang, *On the integral basis of the maximal real subfield of a cyclotomic field*, J. reine angew. Math. 286-287 (1976), 223-226, DOI 10.1515/crll.1976.286-287.223. The elementary argument above specifies its use here.

#### STL.2 Full integral coefficients require the codifferent

**Definition.** The codifferent is the trace-dual fractional ideal

$$\mathfrak D_B^{-1}=
\{a\in B:\operatorname{Tr}_{B/\mathbb Q}(aO_B)\subseteq\mathbb Z\}.$$

Let beta_0,...,beta_(d-1) be the trace-dual basis to the e_j in STL1, so Tr(beta_i e_j)=delta_(ij). The underlying trace-dual and discriminant facts are classical; see A. V. Sutherland, MIT 18.785 (2021), Lecture 12, Definition 12.2, Proposition 12.6 and Theorem 12.17, https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf .

**Theorem STL2.** The rational-coefficient part of the real span of the g_sigma is exactly V_Q, and

$$\boxed{L_{\rm int}=\{F_a:a\in\mathfrak D_B^{-1}\}.}\tag{STL1}$$

The forms f_i=F_(beta_i) are a Z-basis of L_int. Their coefficients at n_0=1 and n_j=ell_j are delta_(ij). For arbitrary rational y_0,...,y_(d-1), the unique form in V_Q with these sampled coefficients is

$$\boxed{F_{\sum_i y_i\beta_i}.}\tag{STL2}$$

It has all Fourier coefficients integral if and only if every y_i is an integer. Removing any one of these d independent sample conditions fails to certify integrality.

**Proof.** If f=sum c_sigma g_sigma has rational sampled coefficients y_j, set a=sum y_i beta_i. The embeddings matrix (sigma(e_j)) is invertible because its squared determinant is the nonzero discriminant of B. The sample equations for f and F_a therefore force c_sigma=sigma(a). This proves the claimed rational descent and uniqueness. For this a, integrality of every coefficient is equivalent by STL1 to Tr(a O_B) subset Z, exactly the codifferent condition. An element of the codifferent has its unique coordinates Tr(a e_i) in the trace-dual basis all integral; conversely integral coordinates make every trace coefficient integral. Hence the f_i form the claimed basis.

For the last assertion, after omitting sample i take a=beta_i/2. All remaining selected coefficients are zero, while the omitted one is 1/2. This is an explicit false positive for the punctured test, not a search argument. It proves necessity of each selected coordinate; it does not assert that every possible set of d Fourier samples is independent.

The trace-dual reconstruction used here is already supplied by the pinned Mathlib trace-dual basis API. It is not reintroduced as a separate formal theorem. The explicit prime-layer integral-image construction in STL.4 below is the formal consumer; the automorphic coefficient-span and cyclotomic identifications remain ordinary proofs.

#### STL.3 Exact saturation index at every prime-power level

**Theorem STL3.** Put

$$\delta_k=\frac{p^{k-1}(k(p-1)-1)-1}{2},\qquad
r_k=\delta_k-(k-1)d=\frac{p^{k-1}(p-2)-1}{2}.$$

Then 0<r_k<d, disc(B)=p^(delta_k), and

$$\boxed{[L_{\rm int}:L_{\rm tr}]=p^{\delta_k},}\tag{STL3}$$

$$\boxed{L_{\rm int}/L_{\rm tr}\simeq
(\mathbb Z/p^k\mathbb Z)^{r_k}\oplus
(\mathbb Z/p^{k-1}\mathbb Z)^{d-r_k}.}\tag{STL4}$$

The factors of order p^0 at k=1 are trivial. If Psi_m is the monic minimal polynomial of t, then the precise fractional ideal is D_B^(-1)=Psi_m'(t)^(-1)O_B.

**Proof.** The cyclotomic polynomial derivative gives discriminant exponent p^(k-1)(k(p-1)-1) for Q(zeta). By STL1, O_(Q(zeta))=O_B[zeta], with relative quadratic discriminant t^2-4. Its absolute ideal norm is p: (zeta-zeta^(-1))^2=t^2-4, and the absolute norm of 1-zeta^2 is p, since zeta^2 is primitive. Discriminant transitivity gives disc(B)=p^(delta_k). Only p ramifies, and it is totally ramified of degree d with residue field F_p. Thus the different is l_m^(delta_k), where l_m is the prime in SGN2. Monogenicity and the derivative formula give D_B=(Psi_m'(t)).

The classical trace-dual index identity is [D_B^(-1):O_B]=disc(B). The injective map a to F_a and STL2 give STL3. Locally the quotient is O_(B,l_m)/l_m^(delta_k), because l_m is principal. Multiplication by p raises l_m-valuation by d. Consequently the F_p dimension of the i-th successive p-layer is d for 1<=i<k, r_k for i=k, and zero thereafter. The elementary-divisor theorem for finite abelian p-groups yields precisely STL4. The inequalities on r_k follow from p>5 and d=p^(k-1)(p-1)/2. This is a classically determined coefficient-field lattice; it is not an additional restriction on the unknown existence of eta.

#### STL.4 Explicit integral coefficient basis at the WSS threshold

**Theorem STL4.** Suppose k=1 and d=(p-1)/2. With t_j as in STL1, the trace-dual basis is

$$\boxed{\beta_0=\frac{2-t_d}{p},\qquad
\beta_j=\frac{t_j-t_d}{p}\quad(1\le j<d).}\tag{STL5}$$

The trace Gram matrix H in the basis e_0=1,e_j=t_j has entries

$$H_{00}=d,\quad H_{0j}=H_{j0}=-1,\quad
H_{ij}=p\delta_{ij}-2\quad(i,j>0),$$

and

$$\boxed{H^{-1}=\frac1p
\begin{pmatrix}3&\mathbf1^{\mathsf T}\\
\mathbf1&I+J\end{pmatrix},\qquad\det H=p^{d-1}.}\tag{STL6}$$

Here J is the all-ones matrix of size d-1.

**Proof.** The sum of all nontrivial pth roots is -1. Hence Tr(t_j)=-1 for 1<=j<p, while Tr(t_0)=2d. The identity t_i*t_j=t_(i+j)+t_(i-j), with t_(-a)=t_a, gives the displayed trace matrix. Multiplication by the asserted inverse gives the identity using p=2d+1. Also 1+sum_(j=1)^d t_j=0, so its columns give exactly STL5. The determinant can be computed by a Schur complement: the lower block pI-2J has eigenvalue3 on the all-ones line and p on its complement; its contribution and the upper Schur factor p/3 give p^(d-1). Alternatively this is STL3 with k=1. This proves the full basis formula, not just linear independence.

**Theorem STL4A.** Write n=d-1 and regard H as a map on Z x Z^n. For an integer vector y, the following conditions are equivalent:

$$\boxed{y\in H\mathbb Z^{n+1}
\quad\Longleftrightarrow\quad
p\mid y_i-2y_0\text{ for every }1\le i\le n.}\tag{STL6a}$$

When they hold, put z_i=(y_i-2y_0)/p. The unique preimage is

$$\boxed{x_0=y_0+\sum_{i=1}^n z_i,\qquad x_i=x_0+z_i.}\tag{STL6b}$$

Thus the quotient map y mapping to (y_i-2y_0 modulo p) identifies Z^(n+1)/HZ^(n+1) with (Z/pZ)^n. The image and reconstruction assertions in fact hold for every n>=0 with p=2n+3, without requiring that p be prime.

**Proof.** For s=sum_i x_i the actual matrix action is y_0=(n+1)x_0-s and y_i=p x_i-x_0-2s. Subtraction gives y_i-2y_0=p(x_i-x_0). This proves necessity and forces z_i=x_i-x_0 in any preimage. Summing these equalities and using the zeroth coordinate then forces x_0=y_0+sum_i z_i. Conversely insert this x_0 and x_i=x_0+z_i into the two displayed matrix rows. Their sum is n*x_0+sum_i z_i, and substitution gives exactly y_0,y_i. This proves existence and uniqueness. The residue map is surjective because y_0=0 permits arbitrary residues in the other coordinates; the exact image calculation identifies its kernel. No matrix inverse or determinant is assumed in this proof.

The source `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.lean` expresses the two-row template on Z x (Fin n -> Z), defines the reconstruction using integer division, and proves its correctness and uniqueness exactly under the displayed divisibility condition. Its theorem does not assume the image characterization or an inverse. Identification of this matrix with the prime-cyclotomic trace form is the ordinary argument of STL4, and no formal claim about an existing WSS packet is made by the arithmetic template.

**Theorem STL5.** For a good split prime ell, write eta(q)=zeta_p^b and interpret b modulo p. The prime coefficients of the integral basis f_j=F_(beta_j) are

$$[\ell]f_0=\begin{cases}
2,&b=0,\\-1,&b=\pm d,\\0,&\text{otherwise},
\end{cases}$$

$$\boxed{[\ell]f_j=\mathbf1_{b=\pm j}-\mathbf1_{b=\pm d}
\quad(1\le j<d).}\tag{STL7}$$

At good inert primes every coefficient is zero. The first coefficient of f_0 is one; all the other f_j have first coefficient zero.

**Proof.** At a split prime A_eta(ell)=t_b. Apply the trace to STL5 after multiplying by t_b, and use t_i*t_b=t_(i+b)+t_(i-b). The trace is p-1 for a t-index zero modulo p and -1 otherwise. For f_0 this gives the three stated cases; for j>0 subtracting the two trace pairs gives p times the stated difference of indicators before division by p. At inert primes A_eta(ell)=0. The first-coefficient assertions are the trace-dual identities against e_0=1. These f_j are usually not Hecke eigenforms; prime coefficient bounds for them do not turn them into new one-dimensional automorphic representations.

**Corollary.** At k=1 the ordinary trace lattice misses exactly (Z/pZ)^(d-1) inside the full coefficient-integral lattice. Modulo p its inclusion has one-dimensional image. The ordinary trace Gram matrix modulo p has rank one.

**Proof.** STL4 at k=1 gives the quotient, which is killed by p, so the image dimension is d-(d-1)=1. Alternatively, using d=-1/2 modulo p, the displayed Gram matrix is -1/2 times the outer product of (1,2,...,2) with itself. This is not the nondegeneracy statement over Q; ramified reduction has changed the pairing.

#### STL.5 Full Hecke algebra and raw-trace content

**Theorem STL6.** The integral algebra generated by the good Hecke operators on V_Q is O_B acting by a mapping to a*A_eta(ell). It preserves L_int. Its action on L_int/pL_int is the regular action of

$$\boxed{O_B/pO_B\simeq\mathbb F_p[\epsilon]/(\epsilon^d),\qquad
\epsilon=t-2.}\tag{STL8}$$

A good generator-rotation prime makes T_ell-2 a nilpotent operator of exact index d on this reduction. In contrast reduction modulo l_m gives the one-dimensional residue field F_p.

**Proof.** The Hecke eigenvalue equation shows T_ell(F_a)=F_(a*A_eta(ell)). All eigenvalues are in O_B, and one generator-rotation Frobenius has coefficient t, so the generated ring is exactly Z[t]. The codifferent is an O_B fractional ideal and is principal by STL3, hence is a free rank-one O_B module. Therefore its reduction modulo p realizes the regular ring representation.

In the cyclotomic ring every conjugate of t is two modulo the prime above p, so the monic integer polynomial Psi_m reduces to (X-2)^d modulo p. Its coefficients reduce into F_p, making this an equality of polynomials, not just an equality at a point. Monogenicity gives STL8. Multiplication by epsilon in the truncated polynomial ring has nilpotence index exactly d. This establishes the algebra at the rational modulus p, and distinguishes it from the prime-ideal reduction used in SGN2.

**Theorem STL7.** The greatest common divisor of the Fourier coefficients of the raw trace F_1 is exactly p^(k-1). Its primitive normalization is F_(1/p^(k-1)), whose first coefficient is (p-1)/2. For a good split prime with rotation exponent b, the raw coefficient is

$$\boxed{\operatorname{Tr}_{B/\mathbb Q}(t_b)=
\begin{cases}
p^{k-1}(p-1),&p^k\mid b,\\
-p^{k-1},&p^{k-1}\mid b,\ p^k\nmid b,\\
0,&p^{k-1}\nmid b.
\end{cases}}\tag{STL9}$$

**Proof.** The real trace is the Ramanujan sum sum_(a mod p^k,p not dividing a)zeta^(ab). Subtract from the sum over all residues the sum over residues divisible by p. Each complete geometric sum is its length or zero according as the corresponding modulus divides b. This gives STL9. Since 1,t_1,...,t_(d-1) is an integral basis and Tr(1)=d, every trace of an integer of B is divisible by p^(k-1). Conversely Chebotarev supplies a good split coefficient t_(p^(k-1)), whose trace is -p^(k-1). Thus the gcd is exact, and the first coefficient after division is d/p^(k-1). This divisibility is caused by the coefficient-field trace; it supplies no new WSS depth.

#### STL.6 The saturated Petersson covolume and its arithmetic boundary

**Theorem STL8.** Let G_eig be the SGN Gram matrix in the normalized eigenbasis. In any Z-basis of L_tr and any Z-basis of L_int, respectively, the Petersson Gram determinants are

$$\boxed{\det G_{\rm tr}=p^{\delta_k}\det G_{\rm eig},\qquad
\det G_{\rm int}=p^{-\delta_k}\det G_{\rm eig}.}\tag{STL10}$$

Consequently, with the reflection fields and regulator normalization of SGN,

$$\det G_{\rm int}=p^{-\delta_k}
[4p^k(p-\chi_5(p))\log\phi]^d
\frac{h(M_{p,k})\operatorname{Reg}(M_{p,k})}
{h(M_{p,k-1})\operatorname{Reg}(M_{p,k-1})}.$$

At the WSS threshold k=1 this simplifies to

$$\boxed{\det G_{\rm int}
=p[4(p-\chi_5(p))\log\phi]^{(p-1)/2}
 h(M_{p,1})\operatorname{Reg}(M_{p,1}).}\tag{STL11}$$

**Proof.** The change-of-basis matrix from the normalized eigenforms to trace forms F_(e_i) is the embeddings matrix (sigma(e_i)); the square of its determinant is disc(B)=p^(delta_k). The trace-dual basis changes this matrix by the inverse trace Gram matrix, so its squared determinant is p^(-delta_k). Apply the real Gram determinant transformation law. Unimodular changes among Z-bases do not change either determinant. Substitution of SGN12 gives the displayed regulator ratio; for k=1 use delta_1=d-1. The determinant is a real quantity involving regulators. Its explicit scalar p-power is not by itself an integral divisibility theorem about the entire determinant.

**Proposition.** STL constructs and saturates the integer-coefficient structure of an existing golden dihedral packet. It does not change the existence condition h_p>=k+1, and supplies no new actual WSS example or non-WSS prime family. In particular L_int being nonzero was derived from the preselected eta, rather than proved without it.

**Proof.** Every spectral form in STL was defined through the packet in SGN, which by ROC requires that original depth condition. The trace-dual argument constructs elements inside that packet; Chebotarev selects auxiliary primes only in its already-existing field. None of the index, local-algebra or determinant calculations asserts that the field or packet exists at a new target p. These formulas do provide a corrected arithmetic normalization for a future independent lattice or congruence obstruction: it must use L_int rather than mistake L_tr or the normalized eigenbasis for the full integer-coefficient lattice.


<a id="wss-ctg"></a>

### CTG. Complete-tower gluing and exact rational Eisenstein congruence depth

#### CTG.1 Retain every nontrivial character in one cyclic quotient

**Definition.** Fix p>5 and k>=1, retain K=Q(sqrt(5)), and assume an actual ordinary ring-class character eta of order m=p^k as in ROC. Thus h_p>=k+1 is a hypothesis. Put D_k=(p^k-1)/2. At the common level 5p^(2k+2), take the unscaled oldvector g_(eta^b)(z), not g_(eta^b)(az), for each b=1,...,D_k. This includes all nontrivial characters of the cyclic quotient, modulo inversion, including characters of smaller order. The forms have distinct good eigenvalue systems and are linearly independent. At each order p^j they are the complete primitive packet D_(p,j). No other inducing fields or Hecke characters are added.

Let C_0(X)=2, C_1(X)=X, C_(a+1)(X)=X C_a(X)-C_(a-1)(X). Let Psi_(p^j) be the monic minimal polynomial of zeta_(p^j)+zeta_(p^j)^(-1). Define

$$Q_k(X)=1+\sum_{a=1}^{D_k}C_a(X),\qquad
E_k=\prod_{j=1}^k B_{p^j},\quad
B_{p^j}=\mathbb Q(\zeta_{p^j}+\zeta_{p^j}^{-1}),$$

$$t=(\zeta_{p^j}+\zeta_{p^j}^{-1})_{j=1}^k,\qquad R_k=\mathbb Z[t]\subset E_k.$$

The rational algebra E_k is a product of fields, not a number field. Write tau for its algebra trace, the sum of the field traces. Classical real-quadratic Hecke induction supplies the ambient forms, as in Tanaka, arXiv:2601.21588v3, Theorem 1.1 and equation (1.1), with the factor-two Fourier normalization already fixed in SGN1. No Petersson-norm assertion of that paper or SGN is an input below.

**Theorem CTG1.** One has

$$\boxed{Q_k(X)=\prod_{j=1}^k\Psi_{p^j}(X),\quad
Q_k(2)=p^k,\quad R_k\simeq\mathbb Z[X]/(Q_k(X)).}\tag{CTG1}$$

This R_k is exactly the integral algebra of good Hecke operators on the complete tower. The Z-span of its actual Fourier coefficient vectors is all of R_k, already using coefficient one and finitely many good split-prime coefficients.

**Proof.** For an odd integer m and z^m=1 with z!=1, the complete geometric sum gives 1+sum_(a=1)^((m-1)/2)(z^a+z^(-a))=0. Also C_a(z+z^(-1))=z^a+z^(-a), by its recurrence. The D_k distinct values zeta_m^b+zeta_m^(-b), b=1,...,D_k, are therefore all roots of the monic degree-D_k polynomial Q_k. Partitioning them by their exact orders proves its factorization. Evaluating C_a(2)=2 proves Q_k(2)=1+2D_k=m. Its distinct irreducible factors identify Q[X]/(Q_k) with E_k and give the integral presentation of R_k.

A good inert prime has coefficient zero throughout the tower. At a split prime with eta(q)=zeta_m^a, the simultaneous eigenvalue is C_a(t), reducing a modulo m and inversion if necessary. At arbitrary n, conjugation pairs ideals of norm n with inverse character values; a fixed ideal has value one because the character order is odd. Thus every simultaneous coefficient belongs to R_k. Conversely, Chebotarev in the already-existing dihedral class field of eta supplies a split generator-rotation prime, whose eigenvalue vector is t. It also supplies coefficients C_a(t), 1<=a<D_k, in distinct selected primes. Together with coefficient one these form an integral basis of R_k: the C_a are monic of degree a, a unitriangular change from the power basis. This proves both algebra and Z-span assertions. It makes no claim of class-field existence or a bound on the selected primes without eta.

#### CTG.2 The successive primitive packets are glued integrally

**Theorem CTG2.** For j<k,

$$\Psi_{p^k}(t_j)=p\quad\text{in }B_{p^j},\qquad
\Psi_{p^k}(X)\equiv p\pmod{Q_{k-1}(X)}.\tag{CTG2}$$

For k>=2 there is a ring isomorphism

$$\boxed{R_k\simeq R_{k-1}\times_{R_{k-1}/pR_{k-1}}O_{B_{p^k}},\qquad
R_{k-1}/pR_{k-1}\simeq\mathbb F_p[e]/(e^{D_{k-1}}).}\tag{CTG3}$$

The map from the new primitive factor to the common quotient sends t_k to 2+e. With S_k=product_(j=1)^k O_(B_(p^j)), the normalization of R_k, the exact additive index is

$$\boxed{[S_k:R_k]=p^{J_k},\qquad
J_k=\sum_{j=1}^{k-1}D_j
=\frac12\left(\frac{p(p^{k-1}-1)}{p-1}-(k-1)\right).}\tag{CTG4}$$

**Proof.** The identity Phi_(p^k)(Z)=Z^(d_k) Psi_(p^k)(Z+Z^(-1)), where d_k=p^(k-1)(p-1)/2, evaluated at a primitive p^j-th root for j<k gives p on the left. The exponent d_k is divisible by p^j, proving the first equality. Since the monic factors of Q_(k-1) are distinct, division by Q_(k-1) proves the second equality integrally.

For monic coprime polynomials f,g over Q, the integer polynomial sequence identifies Z[X]/(fg) with the fiber product of Z[X]/(f) and Z[X]/(g) over Z[X]/(f,g). The intersection ideal is (fg), by rational coprimality and monic integer division. Take f=Q_(k-1), g=Psi_(p^k). CTG2 makes (f,g)=(f,p). Every conjugate of t_j reduces to two above p, so Psi_(p^j)(X) reduces to (X-2)^(d_j); hence Q_(k-1) reduces to (X-2)^(D_(k-1)). This proves CTG3, including the specified homomorphisms. Its additive cokernel has size p^(D_(k-1)). Starting from R_1=O_(B_p) and applying the index formula successively gives CTG4. Thus rational decomposition into packets cannot be substituted for an integral direct product.

#### CTG.3 The full coefficient lattice across different orders

**Definition.** For a in E_k define the rational trace form

$$\mathcal F_a=\sum_{j=1}^k\ \sum_{\sigma:B_{p^j}\hookrightarrow\mathbb R}
\sigma(a_j)g_{\eta^{p^{k-j}},\sigma}.$$

Its nth coefficient is tau(a A(n)). Let Lambda_k be the full lattice of integer Fourier coefficients in this rational tower. Let Lambda_sep be the direct sum of the separately saturated primitive-packet lattices in STL, embedded into the same space. Put R_k^vee={a in E_k:tau(aR_k) subset Z}.

**Theorem CTG3.** The map a to F_a identifies the rational-coefficient part of the real tower span with E_k and

$$\boxed{\Lambda_k=\mathcal F(R_k^\vee),\qquad
[\Lambda_k:\Lambda_{\rm sep}]=p^{J_k}.}\tag{CTG5}$$

With e_0=1, e_i=C_i(t) for 1<=i<D_k, its trace matrix is

$$H_{00}=D_k,\qquad H_{0i}=H_{i0}=-1,\qquad
H_{ij}=p^k\delta_{ij}-2\quad(i,j>0).\tag{CTG6}$$

Consequently

$$\boxed{\operatorname{disc}(R_k)=(p^k)^{D_k-1},\qquad
\Lambda_k/\mathcal F(R_k)\simeq(\mathbb Z/p^k\mathbb Z)^{D_k-1}.}\tag{CTG7}$$

**Proof.** The sampled coefficient vectors in CTG1 are an integral basis of R_k. Their embedding matrix is invertible because Q_k has distinct roots. Solving the sample equations by its trace-dual basis proves rational descent exactly as in STL2, now for the separable product E_k. Integer coefficients are equivalent to tau(aR_k) subset Z because the actual coefficient span is R_k. The separately saturated lattice is F(S_k^vee). Dualizing the finite-index inclusion R_k subset S_k preserves its index, proving CTG5.

The sum over every nontrivial mth root of unity gives tau(C_a(t))=-1 when m does not divide a, and m-1 otherwise, with m=p^k. Use C_i C_j=C_(i+j)+C_(i-j) and C_(-a)=C_a. In the displayed index range no sum i+j is a nonzero multiple of m, and i-j is zero exactly on the diagonal. This proves CTG6. It is exactly the matrix template of STL4A, with n=D_k-1 and 2n+3=m, including composite m. Its explicit integral-image theorem gives quotient (Z/m)^(D_k-1) and determinant m^(D_k-1). That theorem is already the statement of `PrimeCyclotomicTraceImage.integral_image`; this consumer needs no new Lean wrapper. The automorphic and product-algebra identifications in this paragraph remain ordinary mathematics.

#### CTG.4 Exact gluing to the scalar Eisenstein system

**Definition.** Write b(n)=sum_(d|n)chi_5(d). The scalar good-Hecke system has eigenvalue b(ell)=1+chi_5(ell). Adjoin its one-dimensional coefficient module to the tower; no analytic normalization of a selected Eisenstein series is required for this definition.

**Theorem CTG4.** The good-Hecke algebra on the tower plus this scalar system is

$$\boxed{\widetilde R_k\simeq
\mathbb Z[X]/((X-2)Q_k(X))
\simeq R_k\times_{\mathbb Z/p^k\mathbb Z}\mathbb Z.}\tag{CTG8}$$

The map from R_k is evaluation at X=2 modulo p^k. The ideal in R_k generated by all good Hecke discrepancies is (t-2)R_k, and

$$\boxed{R_k/(t-2)R_k\simeq\mathbb Z/p^k\mathbb Z.}\tag{CTG9}$$

The inclusion of the glued algebra into R_k x Z has index p^k.

**Proof.** A split prime acts by (C_a(t),2); an inert prime acts by (0,0). Since C_a(2)=2 and a generator prime gives (t,2), these operators generate exactly Z[(t,2)]. Polynomial evaluation has kernel ((X-2)Q_k), and the sum of the ideals (X-2),(Q_k) gives quotient Z/(Q_k(2))=Z/p^k. The same integer polynomial fiber-product argument as in CTG2 proves CTG8 and the index. Each split discrepancy C_a(t)-2 is divisible by t-2, and the generator discrepancy is t-2 itself. Quotienting gives CTG9. For one isolated primitive packet the identical argument instead gives O_(B_(p^j))/(t_j-2)=F_p, since Psi_(p^j)(2)=p. Thus the complete-tower congruence module has order p^k even though every individual primitive packet has only one p-factor.

#### CTG.5 A normalized integral cusp form and the sharp depth bound

**Definition.** For r>=1 let E_(k,r) be the simultaneous scalar-Eisenstein eigenspace in Lambda_k/p^r Lambda_k: its elements satisfy (T_ell-1-chi_5(ell))f=0 for every good prime ell. Congruence here concerns Fourier coefficients in the specified lattice, not reduction of a real-analytic function pointwise modulo p.

**Theorem CTG5.** The first Fourier coefficient gives an isomorphism

$$\boxed{E_{k,r}\simeq
\{c\in\mathbb Z/p^r\mathbb Z:p^k c=0\}.}\tag{CTG10}$$

In particular this group is cyclic of order p^min(k,r). A normalized class with first coefficient one exists exactly when r<=k and is then unique. No primitive vector in Lambda_k can satisfy the simultaneous Eisenstein congruence modulo p^(k+1).

An explicit normalized integral cusp form attaining depth k is

$$\boxed{f_m=\mathcal F_{-C_{D_k}(t)},\qquad [1]f_m=1.}\tag{CTG11}$$

For (n,p)=1 it has the exact coefficient formula

$$\boxed{[n]f_m=b(n)-m a_D(n),\qquad
 a_D(n)=\#\{\mathfrak a:N\mathfrak a=n,\ \eta(\mathfrak a)=\zeta_m^{D_k}\}.}\tag{CTG12}$$

At a good split prime its coefficient is 2-m if the rotation exponent is +/-D_k, and is two otherwise; at a good inert prime it is zero. All coefficients are integers. The class of f_m generates E_(k,r) for r<=k; for r>k the generator is p^(r-k)f_m modulo p^r.

**Proof.** The perfect pairing between R_k and R_k^vee identifies Lambda_k/p^r Lambda_k with Hom_Z(R_k,Z/p^r). Under this pairing the action of t-2 is precomposition with multiplication by t-2. By CTG9, its annihilated functionals are exactly Hom_Z(Z/p^k,Z/p^r), and such a functional is uniquely determined by its value on one. This proves CTG10, including the stated first coefficient and the primitive-vector bound.

For CTG11, the full-root sum gives tau(-C_D(t))=1, and for 1<=i<D gives tau(-C_D(t)C_i(t))=2. Thus its trace functional on the displayed basis is evaluation of C_i at two. Modulo m it factors through R_k/(t-2), proving the required congruence and normalization. It is integral since -C_D(t) lies in R_k and every trace pairing of elements of R_k is integral.

More explicitly, pair conjugate ideals of norm n. A fixed ideal has character one and contributes one both to b(n) and to f_m. A nonfixed pair with character values zeta^a,zeta^(-a) contributes C_a(t). The identity C_D C_a=C_(D+a)+C_(D-a) and the full-root trace show that its contribution to f_m is two, except at a=+/-D, where it is 2-m. Exactly one ideal in each exceptional pair has character zeta^D, because m is odd and D is a unit modulo m. This proves CTG12; the ideal count of norm n in K is b(n). The same computation gives the good-prime formula. The cyclic group in CTG10 and first coefficient one identify all its generators as stated. Chebotarev gives exceptional auxiliary primes in the existing field, so these exact negative coefficients are not suppressed. This supplies no new target prime or character.

#### CTG.6 Exact finite-precision scalar characters

**Theorem CTG6.** Every unital homomorphism R_k -> Z/p^r has t=2 modulo p. The number of such homomorphisms is p^(r-1) for 1<=r<=k and zero for r>k. For the augmented algebra Rtilde_k the number is

$$\boxed{p^{\min(k,r-1)}.}\tag{CTG13}$$

Its only Z_p-valued character is the scalar Eisenstein evaluation t=2.

**Proof.** Each monic shifted polynomial Psi_(p^j)(2+U) reduces to U^(d_j) modulo p and has constant term p. Its degree d_j is at least three for p>5. Hence for u in pZ_p, every nonconstant term has valuation at least two and

$$\Psi_{p^j}(2+u)\equiv p\pmod{p^2},\qquad
v_p(Q_k(2+u))=k.$$

Reduction modulo p of Q_k is (X-2)^(D_k), so a homomorphism has image t=2+u with u divisible by p. For the cusp algebra, Q_k(2+u)=0 modulo p^r holds exactly when r<=k; every such residue u then works, giving p^(r-1) choices. For the augmented algebra the condition is u Q_k(2+u)=0. Thus u must be a multiple of p^max(1,r-k), giving CTG13. Over Z_p the factor Q_k(2+u) is nonzero, so u=0. These are scalar characters with target Z/p^r or Z_p; the genuine cuspidal characters take values in ramified cyclotomic integer rings. This statement does not rule out those ramified characteristic-zero characters.

#### CTG.7 What is and is not inferred about WSS

**Corollary CTG7.** Fix a prime p>5 and take the complete finite p-power ring-class tower in ROC, whose largest character order is p^(h_p-1). If h_p=1 there is no such cuspidal tower. Otherwise the maximum rational p-adic Eisenstein congruence depth of a primitive integer-coefficient vector in this tower is exactly h_p-1.

**Proof.** Apply CTG5 at k=h_p-1. ROC7 gives precisely the available nontrivial orders p,...,p^k. Higher congruence is excluded within their full coefficient-integral span by CTG10. Conversely CTG11 supplies a normalized vector attaining k. The theorem concerns the complete finite-order, fixed-golden tower, not all Maass forms at the same level.

The inter-packet gluing in CTG3 is an extra step beyond the single-packet lattice STL. It does not change any of STL's statements. For the abstract coefficient tower p=7,k=2, the total dimension is24, the two primitive dimensions are3 and21, and [Lambda_2:Lambda_sep]=7^3. The complete congruence module is Z/49, whereas each isolated primitive module gives Z/7. These algebraic examples do not assert the existence of a golden character of order49 or a WSS prime at seven.

The finite-orbit discipline in the separate CarlitzFiveOrbit result is methodologically relevant: projecting to one primitive factor before doing integer elimination can lose compatibility conditions. Its characteristic19 certificate is not a theorem about these characteristic-zero Hecke orders. Here the complete-orbit polynomial Q_k and its integer fiber products are proved directly; no Carlitz theorem is imported.

For comparison, Fretwell-Roberts, *Hilbert modular Eisenstein congruences of local origin*, arXiv:2411.06987v2 (March 3, 2026), Journal of Number Theory280(2026),861-896, proves congruence existence results in parallel holomorphic weight at least three. Those weight hypotheses are absent from the parameter-zero, weight-zero Maass family here. Its existence theorem is not used to create the character eta. Source roles and the current version locators are recorded in the accompanying Library notes.

All spectral conclusions of CTG start with an existing eta, so CTG7 is an exact recovery of the original depth, not an independently proved bound on it. A new WSS prime-family decision would require an independent restriction or construction for the complete integral Hecke system, with all the weight, conductor, evenness and fixed-field conditions retained. Neither the universal polynomial model nor its finite-precision scalar characters establish such existence. No Petersson-norm inequality, general mod-p modularity theorem or unknown class-group order is used to choose a branch.


<a id="wss-hcr"></a>

### HCR. One-prime Hecke reconstruction and the exact observable subfield

#### HCR.1 A single actual auxiliary prime

**Definition.** Retain an existing ordinary golden ring-class character eta of exact order m=p^k from ROC, with p>5 and k>=1. Thus the actual hypothesis h_p>=k+1 remains in force. Put q=p^(k-1), h=(p-1)/2 and d=hq. Let zeta be a primitive mth root of unity, t=zeta+zeta^(-1), B=Q(t), and Psi_m the monic minimal polynomial of t. Retain the SGN-normalized forms g_sigma and the rational trace forms

$$\mathcal F_c=\sum_{\sigma:B\hookrightarrow\mathbb R}\sigma(c)g_\sigma,
\qquad c\in B.$$

The notation F_n without a calligraphic letter continues to denote a Fibonacci number. Choose a good split rational prime ell, ell not dividing 5p, whose rotation Frobenius generates the cyclic group of order m. Relabel zeta so that eta(q_ell)=zeta at one of the two primes above ell. Chebotarev in the already-existing class field supplies such ell; this does not construct eta and gives no bound for the least such ell here.

Define monic polynomials P_0(X)=1, P_1(X)=X and P_(n+1)(X)=X P_n(X)-P_(n-1)(X). These equal the classical Chebyshev polynomials U_n(X/2). Define D_0(X)=2, D_1(X)=X and the same recurrence for D_n; then D_n(t)=zeta^n+zeta^(-n).

**Lemma HCR1.** The exact prime-power coefficients and their generating function are

$$A_\eta(\ell^n)=P_n(t)=\sum_{j=0}^n\zeta^{n-2j},\qquad
\sum_{n\ge0}P_n(t)Z^n=\frac1{1-tZ+Z^2}.\tag{HCR1}$$

The elements P_0(t),...,P_(d-1)(t) are a Z-basis of O_B.

**Proof.** The ideals of norm ell^n are q_ell^j sigma(q_ell)^(n-j), for 0<=j<=n. Their character values sum to the displayed expression. It satisfies the stated recurrence and initial values, which also prove the formal generating function. Each P_j is monic of degree j with integer coefficients. Thus this family is a unitriangular change of the integral power basis 1,t,...,t^(d-1) established in STL1. All equalities are exact; no asymptotic Hecke estimate is used.

The polynomial generating function is classical, NIST DLMF 18.12.10. The input that these ideal sums define the specified Maass forms is the real-quadratic Hecke construction in D. Tanaka, *Explicit Construction of Maass Wave Forms and Their Petersson Inner Products*, arXiv:2601.21588v3, Theorem 1.1 and its defining Fourier expansion. This subsection uses neither that paper's Petersson norm constant nor a nonvanishing assertion at an unknown WSS target. Source roles are recorded in `Library/notes/tanaka2026maass.md`.

#### HCR.2 The reciprocal numerator and a constructive inverse

**Theorem HCR2.** For c in B, let R_c(X) be the unique polynomial of degree less than d with

$$R_c(t)=c\Psi_m'(t).$$

Put s_n(c)=[ell^n]F_c=Tr_(B/Q)(c P_n(t)). Then

$$\boxed{\sum_{n\ge0}s_n(c)Z^n
=\frac{N_c(Z)}{\Phi_m(Z)},\qquad
N_c(Z)=Z^{d-1}R_c(Z+Z^{-1}).}\tag{HCR2}$$

N_c is a rational polynomial of degree at most 2d-2 and has reciprocity of the fixed width 2d-2:

$$N_c(Z)=Z^{2d-2}N_c(Z^{-1}).$$

Every rational polynomial with this width-reciprocity occurs for a unique c. Moreover

$$\boxed{\mathcal F_c\in L_{\rm int}
\iff N_c\in\mathbb Z[Z]
\iff s_0(c),...,s_{d-1}(c)\in\mathbb Z.}\tag{HCR3}$$

The width is fixed even when the leading coefficients vanish; its value is not claimed to be the actual degree of every N_c.

**Proof.** Let t_sigma be the conjugates of t. Partial fractions and Lagrange interpolation give

$$\sum_\sigma\frac{\sigma(c)}{X-t_\sigma}
=\frac{R_c(X)}{\Psi_m(X)},$$

because the numerator evaluated at t_sigma is sigma(c) Psi_m'(t_sigma). Substitute X=Z+Z^(-1), multiply by Z^(-1), and use

$$Z^d\Psi_m(Z+Z^{-1})=\Phi_m(Z)
=1+Z^q+\cdots+Z^{(p-1)q}.$$

This proves HCR2 as a formal power-series identity. The elements Z^(d-1) and Z^(d-1)(Z^j+Z^(-j)), 1<=j<=d-1, are a basis of the polynomials with this reciprocity. They correspond to 1,D_1,...,D_(d-1), an integral triangular basis of polynomials of degree less than d. This proves the bijection and N_c integral iff R_c integral.

The monogenic trace-dual formula is D_B^(-1)=Psi_m'(t)^(-1)O_B; equivalently it follows from Lagrange interpolation by pairing the power basis with the coefficients of Psi_m(X)/(X-t). Since O_B=Z[t], R_c integral is equivalent to c belonging to the codifferent, and hence to F_c belonging to L_int by STL2. Alternatively P_0(t),...,P_(d-1)(t) are already an integral basis by HCR1, so their d integer traces are exactly the defining codifferent test. These are classical trace-dual facts, used here with the actual single-prime coefficients.

**Theorem HCR3.** Given arbitrary integers y_0,...,y_(d-1), define, for 0<=j<=d-1,

$$n_j=\sum_{a=0}^{\lfloor j/q\rfloor}y_{j-aq},\qquad
n_{2d-2-j}=n_j.$$

Set

$$N_y(Z)=\sum_{j=0}^{2d-2}n_j Z^j,$$

$$R_y(X)=n_{d-1}+\sum_{j=0}^{d-2}n_jD_{d-1-j}(X),\qquad
c_y=R_y(t)/\Psi_m'(t).\tag{HCR4}$$

Then F_(c_y) is the unique form in the rational packet with [ell^j]F_(c_y)=y_j for 0<=j<d, and all its Fourier coefficients are integers. The same construction with rational y gives the unique rational-packet form. Omitting any one of these d selected samples leaves a nonintegral form with all remaining selected coefficients integral.

**Proof.** The reciprocal assignment is consistent at its central coefficient. The first d coefficients of Phi_m(Z) times sum y_j Z^j are precisely the n_j displayed above. Therefore N_y/Phi_m has the required first d coefficients. The expansion in D_j gives Z^(d-1)R_y(Z+Z^(-1))=N_y. HCR2-HCR3 prove existence and integrality. If two forms have the same prefix, their traces against the full basis P_j(t) agree; nondegeneracy of the trace pairing makes their c parameters equal. For omitted sample i, take the rational prefix with y_i=1/2 and all other entries zero. The construction gives a form with exactly that nonintegral sampled coefficient. This proves sharpness of these linear sampling conditions. It does not claim that arbitrary d Fourier positions are independent or bound the height ell^(d-1).

#### HCR.3 The full integer period and the minimal temporal recurrence

**Definition.** For the single-prime sequence set b_0=0 and b_r=s_(r-1) for 1<=r<m, and regard b as a function on Z/mZ.

**Theorem HCR4.** The prime-power sequences of L_int are in bijection with the integer functions b on Z/mZ satisfying

$$\boxed{b_{-r}=-b_r,\qquad
\sum_{j=0}^{p-1}b_{r+jq}=0\quad(r\in\mathbb Z/q\mathbb Z).}\tag{HCR5}$$

In this correspondence s_n=b_(n+1 mod m) for all n>=0. The first d values b_1,...,b_d are free integer coordinates. Every nonzero rational sequence in this family has exact period m and minimal homogeneous constant-coefficient recurrence order 2d over Q, even though those d samples determine it within the specified family.

**Proof.** From HCR2 and Phi_m=(1-Z^m)/(1-Z^q),

$$\sum_{r\ge1}b_rZ^r=\frac{B_c(Z)}{1-Z^m},\qquad
B_c(Z)=ZN_c(Z)(1-Z^q).$$

The degree of B_c is at most m-1 and its constant term is zero. Width-reciprocity of N_c is equivalent to Z^m B_c(Z^(-1))=-B_c(Z), giving oddness. Divisibility by 1-Z^q is equivalent to zero sums of coefficients in each residue class modulo q. Conversely, start with an odd integer b having these fibre sums. Then B(Z)=sum_(r=0)^(m-1)b_rZ^r is divisible by 1-Z^q in Z[Z], since the latter is monic up to sign. Its quotient has zero constant term, so N=B/[Z(1-Z^q)] is an integer polynomial of degree at most 2d-2. The oddness equation makes N width-reciprocal. HCR2-HCR3 supply a unique c and the asserted entire sequence. HCR3 gives its first-d parametrization.

For nonzero rational c, N_c is nonzero with degree below deg(Phi_m)=2d. Irreducibility of the cyclotomic polynomial implies gcd(N_c,Phi_m)=1 in Q[Z]. Hence Phi_m is the reduced generating-function denominator. Any eventual homogeneous rational linear recurrence must have a characteristic polynomial whose reversed polynomial is divisible by Phi_m, so its order is at least 2d; HCR2 realizes that order. A period T would make the reduced denominator divide 1-Z^T, forcing m|T. Since period m has already been proved, it is exact. The rationality assumption is retained in the minimal-recurrence assertion; it is not asserted for arbitrary real linear combinations of individual conjugate sinusoids.

#### HCR.4 Explicit completion and a sharp error-amplification factor

**Theorem HCR5.** Starting from any prescribed b_1,...,b_d, the only missing positive representatives in HCR5 are r=d+a, 1<=a<=(q-1)/2. They are given by

$$\boxed{b_{d+a}=
\sum_{j=1}^{h}b_{jq-a}-\sum_{j=0}^{h-1}b_{jq+a}.}\tag{HCR6}$$

Together with b_0=0 and oddness, this is a direct integer reconstruction of the entire period. The corresponding linear map from the prefix with its maximum norm to the full period with its maximum norm has exact operator norm one for k=1 and p-1 for k>=2. The same bounds hold for differences of two prefixes, and hence for bounded real input errors in this fixed linear extension map.

**Proof.** In the fibre of a modulo q, the positive representatives are a+jq, 0<=j<=h, and the negative representatives are the negatives of jq-a, 1<=j<=h. Solving its zero-sum equation for b_(hq+a) gives HCR6. Every index on the right lies between one and d. The fibre with residue zero has zero sum automatically by oddness; the remaining fibres follow from these equations and their negatives. Thus all constraints hold and uniqueness follows either directly or from HCR4.

For a fixed a, the 2h=p-1 indices on the right are distinct: equality across the two lists would require 2a to be a nonzero multiple of q, whereas 0<2a<q. Their coefficients are exactly +1 or -1. The reconstruction thus has row sums of absolute values at most p-1. When k>=2 a missing row exists; assigning its p-1 prefix entries their respective coefficient signs attains p-1, with prefix norm one. When k=1, q=1 and no missing positive row exists; the full period consists only of the original coordinates, their negatives and zero, giving norm one. These are bounds for the chosen prime-power coefficient subsequence, not a uniform norm bound for all Fourier coefficients of the form.

**Example.** For m=49, q=7 and d=21, one missing coordinate is

$$b_{22}=b_6+b_{13}+b_{20}-b_1-b_8-b_{15}.$$

Its maximum amplification is six. This is an abstract cyclotomic recurrence identity. It asserts neither the existence of a golden character of order 49 nor a WSS prime at seven.

#### HCR.5 Non-generators expose exactly a relative trace

**Theorem HCR6.** Let ell be any good split prime for an existing order-p^k packet, and suppose eta(q_ell) has exact order p^s, with 1<=s<=k. Put

$$B_s=\mathbb Q(\zeta_{p^s}+\zeta_{p^s}^{-1}),\qquad
 d_s=p^{s-1}(p-1)/2,$$

viewing B_s as the corresponding subfield of B=B_k. All coefficients [ell^n]F_c depend exactly on

$$c_s=\operatorname{Tr}_{B/B_s}(c).$$

The single-prime observation map has rational rank d_s and kernel dimension d-d_s. On coefficient-integral lattices its image is the full codifferent lattice of B_s, and its kernel is free of rank d-d_s.

**Proof.** The eigenvalue t_ell belongs to B_s and generates its full integer ring. For every n,

$$\operatorname{Tr}_{B/\mathbb Q}(cP_n(t_\ell))
=\operatorname{Tr}_{B_s/\mathbb Q}(c_sP_n(t_\ell)).$$

The first d_s of these polynomials give a full basis of O_(B_s), so they detect c_s exactly. The field trace is surjective in characteristic zero, giving the rational rank. It remains to show

$$\operatorname{Tr}_{B/B_s}(\mathfrak D_B^{-1})=\mathfrak D_{B_s}^{-1}.$$

The inclusion from left to right follows by composing traces. Conversely O_(B_s) is a saturated Z-submodule of O_B: if an integer multiple of x in O_B lies in B_s then x lies in B_s, hence in O_(B_s). Its quotient is therefore a finitely generated torsion-free abelian group, and is free. Any integral functional on O_(B_s) extends to O_B after choosing a free complement. Represent the extension by trace against c in D_B^(-1). Its restriction is trace against Tr_(B/B_s)c, proving surjectivity onto D_(B_s)^(-1). The exact sequence of free abelian groups then gives the integral kernel rank. No cyclic-order or semisimplified residue observation is substituted for this full trace map.

**Boundary cases.** If eta(q_ell)=1 at a split good prime, then

$$[\ell^n]\mathcal F_c=(n+1)\operatorname{Tr}_{B/\mathbb Q}(c).$$

At an inert good prime the coefficient is Tr(c) for even n and zero for odd n. In both cases the observation rank is one, with kernel dimension d-1. The split identity case is not claimed to be periodic in n.

**Proof.** The split identity case is P_n(2)=n+1. Inert ideal norms occur only in even powers of ell; the unique such ideal is a rational principal ideal and has character value one. The trace map from the codifferent onto Z is surjective by the same functional-extension argument applied to Z subset O_B.

**Corollary.** For any nonempty set of good primes, when only their power coefficients and the coefficients at products of their powers are retained, let p^s be the largest nontrivial rotation order among the split primes. If such an order exists, all these data have exactly the kernel Tr_(B/B_s)c=0. If none exists, the kernel is Tr_(B/Q)c=0. In particular, for k>=2, any collection avoiding generator rotations leaves a kernel of dimension at least d-d/p, regardless of how many powers are observed.

**Proof.** All the observed eigenvalues lie in the largest of the nested subfields B_s, and multiplicativity puts the product coefficients in the same field. One prime of that largest order already spans O_(B_s) through its power coefficients by HCR1. Thus the common observable coefficient algebra has precisely this field and the asserted kernel. Identity and inert primes add only rational coefficients. For k>=2 the largest proper subfield in this tower has degree d/p. This is a restriction on the stated observation set, not on all possible arithmetic methods.

#### HCR.6 Relation to the existing trace-image formalization

**Proposition HCR7.** At k=1, let y_j=[ell^j]F_c, 0<=j<d, be the single-prime prefix of a coefficient-integral form. Then

$$\boxed{\mathcal F_c\in L_{\rm tr}
\iff y_j\equiv(j+1)y_0\pmod p\quad(1\le j<d).}\tag{HCR7}$$

**Proof.** Set z_0=y_0, z_1=y_1, and z_j=y_j-y_(j-2) for j>=2. The polynomial identities D_1=P_1 and D_j=P_j-P_(j-2) show that z_j=Tr(c e_j) for the trace basis of STL4. Its existing integral-image theorem says c in O_B exactly when p divides z_j-2z_0 for j>0. Those conditions are y_1=2y_0 modulo p and y_j-y_(j-2)=2y_0 modulo p. Induction on the even and odd indices gives exactly HCR7, and the converse follows by subtraction. This does not require a new Lean theorem: it is an ordinary consumer of `PrimeCyclotomicTraceImage.integral_image` together with the displayed Hecke coefficient recurrence. The existing Scribe is supplemented with this relationship while its formal statement is left unchanged.

#### HCR.7 What this reconstruction does not decide

**Proposition.** HCR1-HCR7 give a constructive complete description of the single-prime coefficient data and their integral lattice for an existing packet. The integer periodic sequences in HCR5 can be constructed abstractly for every prime p>5 and every k>=1, without constructing a golden ring-class character. They are therefore not, by themselves, WSS certificates.

**Proof.** HCR3-HCR5 use only the cyclotomic polynomial, rational trace pairing and explicit integer coefficients once the spectral interpretation is omitted. Those objects exist for every such p and k. Interpreting them as Fourier coefficients of the specified global Maass packet requires eta in X_(p,k), equivalently the original h_p>=k+1 by ROC. No theorem in HCR establishes that premise independently. A new WSS decision would require constructing or excluding that global extension, with all arithmetic and automorphic compatibility conditions retained. The first-d integrality test presupposes membership in this rational packet; it is not a Sturm bound for arbitrary Maass forms or a certificate of global automorphy from a finite prefix. Nor is a computational speedup asserted: HCR uses one auxiliary prime but reaches exponent d-1, and provides no bound on the size of that prime.


[Return to the problem dossier](../../Problems/wall-sun-sun-golden-unit-lift.md).
