# The370-label conditional certificate transfers to arbitrary ten odd primes

The complete ten-prime survivor bound of [Report635](635-a-thirty-label-conditional-core-admits370-missing-originals.md) holds on any ten increasing odd primes, provided its central role relations and exponent inventory are preserved. The target primes need not contain3 or5. For every admitted finite family, with arbitrary permitted phases and finite heights, its Haar survivor density is at least

    h=3365813748958907912564595063607
        /102794609838333443840409600000000000 >1/31000.       (PT1)

This removes the literal-prime restriction of Report635. It does not remove the fixed relative STAR/mask geometry, admit the remaining33 low-square labels, or allow arbitrarily many prime coordinates. The proof is an ordinary deduction using [Report628](628-digit-injections-transport-free-endpoint-heads-and-common-sources.md)'s digit pullback and finite averaging. Its additional obligation is a single family-wide prefix-tree alignment of the distinguished central roles. No new Lean verification is asserted.

## 1. Exact target domain

Let

    p=(3,5,7,11,13,17,19,23,29,31),
    r_1<...<r_10 be any ten odd primes,
    alpha=r_1, beta=r_2, Q_r={r_3,...,r_7}.

In particular r_i>=p_i. The target family is finite; every numerical modulus is greater than1, is supported on these ten primes, and occurs at most once. Each present original has one globally fixed residue. Exponents refer to the same ordered coordinates throughout.

At the alpha coordinate choose two distinct first-digit roles A_alpha,B_alpha. At beta choose three pairwise distinct roles A_beta,B_beta,C_beta. Choose a designated second digit u_alpha below B_alpha and u_beta below C_beta. Digits are the usual least-significant-first prime-power digits. Impose the following relations on every indicated original that is present:

| Numerical original | Required central prefix |
| --- | --- |
| alpha | A_alpha |
| beta | A_beta |
| alpha beta | (B_alpha,B_beta) |
| alpha q, alpha q² | B_alpha |
| beta q, beta q² | C_beta |
| alpha beta q | (B_alpha,C_beta) |
| alpha²q | (B_alpha,u_alpha) |
| beta²q | (C_beta,u_beta) |

These roles are shared across q in Q_r exactly as indicated. All outside components of these originals are arbitrary. The table fixes neither an outside endpoint nor a relation between different numerical originals' outside residues. Central square and higher pure originals have arbitrary phases; all other pure phases and finite heights are unrestricted. When alpha or beta itself is absent, its listed first role is only an auxiliary forbidden root for the sufficient source construction.

The complete exponent inventory is Report635's, transported coordinatewise: it includes the table's retained originals, all120 retained pair originals, its370 additional low-square originals, and every inherited mixed original on the first seven coordinates satisfying

    maximum exponent>=3, or both central exponents<=1, or support size>=5.

All originals touching one of r_8,r_9,r_10 remain unrestricted. The120 pair phases, the370 added phases and every inherited free phase are arbitrary independently, each fixed once for its numerical label. Missing slots are allowed. The complement within the403 low-square gap remains exactly

    alpha² beta, alpha beta², alpha² beta²;
    alpha² q²;
    alpha² qs, q<s in Q_r;
    alpha² beta q, alpha beta² q, alpha² beta² q.

Thus no missing slot has been hidden by changing primes. A table of relative roles is a hypothesis, not an assertion that every unrestricted family can be put in this form.

## 2. One digit injection pulls back the entire family

Choose finite resolving heights H_i>=2 covering all originals. Let X_p and X_r be products of the corresponding p_i- and r_i-symbol digit alphabets. For every coordinate i and digit j choose a target shift s_ij and define

    F_s(x)_ij=x_ij+s_ij mod r_i.

Since p_i<=r_i each digit map is injective. Use this SAME map for all originals and all queries. A target prefix cylinder has either empty preimage or one source prefix cylinder with exactly the same exponent vector. CRT makes the nonempty preimage one residue class modulo the corresponding source numerical modulus.

Distinct target numerical moduli have distinct exponent vectors; their nonempty preimages are therefore distinct source numerical moduli. A target original never splits into different residues in different cells or queries. Empty preimages need no deletion. There is no assertion of a ring homomorphism between unequal primes.

A distinguished target first role is visible when it lies in the corresponding first-digit injection image. Its source inverse is then unique. Distinct visible roles have distinct inverses. A distinguished second role is visible only when its parent first role and that second digit are both visible. Hence every surviving table prefix retains all of its prescribed equality and inequality relations, but its symbols need not yet have Report635's canonical names.

## 3. One prefix-tree permutation aligns every visible role

At the ternary source there are only two distinguished first roles. Extend their partial injective inverse assignment, if necessary, to two distinct symbols of{0,1,2}. A permutation of this alphabet can send these completed roles to

    A_alpha ->2, B_alpha ->0.

At the quinary source complete the at most three visible inverses to three distinct symbols of{0,1,2,3,4}, and send them to

    A_beta ->4, B_beta ->0, C_beta ->2.

The completions exist because there are at most two roles in the three-symbol source and at most three in the five-symbol source. Invisibility does not authorize identifying two distinguished roles.

If the designated alpha child is visible, apply a second-digit permutation under its B_alpha parent that sends its source inverse to0. Do the same for the visible beta child under C_beta. If the parent or child is invisible, choose an auxiliary child once. All second digits under other parents and all later digits can be left unchanged.

Together these choices define ONE source prefix-tree automorphism phi_s, applied to the entire pulled-back family. Each first-digit map and each child permutation is bijective. Thus at every finite height phi_s is a bijection, preserves Haar measure and sends each prefix cylinder to one prefix cylinder of the same length. All later suffix digits remain unchanged. It is not a separate renaming for each original.

After applying phi_s, every nonempty table original has Report635's canonical central prefix: first pure roots2mod3 and4mod5; central15 rectangle(0,0); row role0; column role2; joint role(0,2); square leaves0mod9 and2mod25. In Report635's leaf indices these last two are l=0 and m=10. The arbitrary phases of all other originals remain arbitrary permitted phases. Exponent inventory and numerical-modulus identities are unchanged.

Some table originals may have disappeared under F_s. Report635 permits missing slots. A missing first pure root, central mask or star slot can be handled by one auxiliary deletion fixed for this source family, using the completed roles above and arbitrary permitted outside endpoints. Such a deletion only shrinks a witness; it does not alter any present original or become a new original of the target family. Higher pure and all free mixed phases are transported by the same phi_s, so no conflict is introduced by this padding.

Consequently the transformed family is admissible for Report635 for EVERY fixed s. This simultaneous alignment is the additional stability fact beyond the free-role transport in Reports628 and630.

## 4. Apply the reference bound before averaging

Let U_r be the target survivor and U_s=F_s^(-1)(U_r). The survivor of the nonempty transformed original family is exactly phi_s(U_s). Any auxiliary deletions used in its proof only produce a subset of this survivor. Report635 and Haar preservation therefore give

    H_p(U_s)=H_p(phi_s(U_s))>=h                 for every s.       (PT2)

The source, auxiliary roles and phi_s may depend on s. There is no choice of a different source for different queries in this inequality: Report635 is applied to one whole transformed family. No uniformity of phi_s as s varies is required, since it is measure-preserving separately for each s.

Choose all target shifts independently and uniformly. For every fixed source x, F_s(x) has exactly the product uniform law on X_r. Finite double counting yields

    H_r(U_r)=E_s H_p(F_s^(-1)(U_r))>=h.                       (PT3)

This average uses the original F_s. Its Haar identity is unaffected by the s-dependent alignment, because phi_s was removed in PT2 before averaging. The argument applies to every finite set of resolving heights, so it introduces no maximum exponent bound and requires no infinite-limit exchange. This proves PT1.

The result concerns Haar survival. It does not claim that the reference512 cost coefficients numerically equal their target-prime analogues. Nor does it transfer an undeclared outside-owner interface or assert that arbitrary STAR incidence can be aligned with the table.

## 5. Finite alignment checks and their scope

The [portable alignment checker](../../frontier/cover-geometry/conditional370_prefix_role_transport.py) and its [data](../../frontier/cover-geometry/conditional370_prefix_role_transport.json) exhaust all13 ternary and136 quinary partial injective first-role assignments. Including every possible visible or absent designated child gives40 ternary and661 quinary joint cases. The same tree map is checked on every role cylinder, on all source words of lengths1,2,3, and for bijection, prefix preservation and unchanged later suffixes. It passes11621 explicit checks under

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/conditional370_prefix_role_transport.py

These checks verify the finite alignment implementation. Arbitrary target alphabets, all finite heights, global original identity and the uniform Haar conclusion follow from the ordinary arguments above, not from a finite prime scan. The positive reference bound is reused from Report635; it is not recomputed or claimed as a new formal theorem here.

An independent reconstruction, importing no producer, passes14731 checks. It independently exhausts the701 role/child cases, reconstructs two-sided inverses, verifies simultaneous prefix-cylinder covariance and Haar prefix masses through depth3, and checks the403=370+33 exponent partition and the rational bound PT1. This supplements the ordinary proof and does not enlarge its scope.
