# Fixed early original phases give core margins at every finite height

Fix the old and first-layer child digit patterns of [Chapter20](../../problem-details/20-original-ap-three-color-intersections-can-exceed-the-residual-threshold.md), but allow all four core heights and the ternary height to be arbitrary finite positive integers. Every later original residue is unrestricted. The complete actual old survivor set then contains a point whose original weighted completion load is at most

\[
 \frac{444189}{313630}
 =\frac32-\frac{13128}{156815}.
 \tag{FE1}
\]

There is also a set of positive Haar mass on which a uniform completion margin holds, with all constants independent of these heights. This supplies an actual weighted core probability law for subsequent tail constructions. The deduction is an ordinary mathematical result with an exact coefficient certificate; it is not a Lean certification, an arbitrary-early-phase theorem, or a new noncoverage range.

## Original classes and one probability law

Let \(P=(5,7,11,13)\), let \(h_q\ge1\), and put \(Q=\prod_{q\in P}q^{h_q}\). For each nonempty support \(I\subseteq P\) and each tuple \(1\le v_q\le h_q\), put \(a=\prod_{q\in I}q^{v_q}\). The old original class modulo \(a\) has the Chapter20 old digits \(r_{I,q}^{(0)}\), interpreted literally as

\[
 x\equiv r_{I,q}^{(0)}q^{v_q-1}\pmod {q^{v_q}}
 \qquad(q\in I).
 \tag{FE2}
\]

All these old classes are present. The first-layer class modulo \(3a\), when present, has the Chapter20 new cofactor digits \(r_{I,q}^{(1)}\) in (FE2); its residue modulo 3 can be chosen arbitrarily for each original modulus. Any first-layer classes may be omitted. For each \(2\le e\le H\) and each \(a\mid Q\), \(a>1\), allow at most one original residue \(\alpha_{3^ea}\) modulo \(3^ea\), with no phase restrictions. These are actual CRT classes, not independently reassigned labels. The modulus \(a=1\), comprising pure powers of 3, is excluded from the completion load.

Let \(S\subseteq\mathbb Z/Q\mathbb Z\) avoid every old original class, and let \(\mu\) be uniform on this complete set. It is nonempty: zero avoids (FE2). Write

\[
 N_e(x)=\sum_{\text{present }3^ea,\ a>1}
       1_{x\equiv\alpha_{3^ea}\ (\mathrm{mod}\ a)},\qquad
 g=N_1,\qquad
 \ell_H=\sum_{e=1}^H3^{1-e}N_e.
 \tag{FE3}
\]

The original completion threshold is \(B_H=(3+3^{1-H})/2\). All expectations below use this same \(\mu\), including every unrestricted later layer.

## A coefficient bound retaining original multiplicities

Put \(w_q=(q^{h_q}-1)/(q-1)\) and \(u_q=1/w_q\). Group a nonzero residue modulo \(q^{h_q}\) by its first nonzero base-\(q\) digit. A specified nonzero digit group has \(w_q\) residues; the zero residue has one. The old pure classes delete precisely digit 1, leaving the alphabets \(\{0,2,\ldots,q-1\}\).

Every exponent tuple is present in the full old and first-layer pattern families. An old support pattern therefore forbids exactly its digit product cell. At a matching new support pattern, an actual residue has a unique first nonzero depth in each support coordinate. Consequently exactly one original cofactor label with this support is hit. Thus the full first-layer count \(g_*\) on each quotient cell is the **number of matching support patterns**, rather than the number of colors or merely a union indicator. There are \(4\cdot6\cdot10\cdot12=2880\) cells.

For a zero-coordinate mask \(Z\), in bit order \((5,7,11,13)\), let \(D_Z\) count surviving quotient cells and let \(N_Z\) sum \(g_*+1_{g_*>0}\) over them. With \(u^Z=\prod_{q\in Z}u_q\), define

\[
 D(u)=\sum_ZD_Zu^Z,\qquad N(u)=\sum_ZN_Zu^Z.
\]

In mask order 0 through 15, exact enumeration of the fixed source patterns gives

```text
D = [1191,469,274,98,145,54,32,11,117,44,26,9,14,5,3,1]
N = [2066,394,314,40,202,32,28,2,170,28,24,2,16,2,2,0]
2066 D - 1191 N =
    [0,499700,192110,154828,58988,73452,32764,20344,
     39252,57556,25132,16212,9868,7948,3816,2066]
```

The cell masses give \(|S|=(\prod_qw_q)D(u)\) and
\(E_\mu[g_*+1_{g_*>0}]=N(u)/D(u)\). Every displayed slack coefficient is nonnegative and \(D(u)>0\), proving for every height tuple

\[
 E_\mu g+\Pr_\mu(g>0)
 \le E_\mu g_*+\Pr_\mu(g_*>0)
 \le\frac{2066}{1191}.
 \tag{FE4}
\]

The first inequality permits missing first-layer labels. The proof retains the fixed complete old family; it does not permit arbitrary changes to old phases or substitute a chosen subset for \(S\).

## An actual minimum despite arbitrary later phases

[Chapter19, KE1 and KE7](../../problem-details/19-five-prime-parent-envelopes-and-the-cofactor-allocation-barrier.md) bound the sum of maximal cylinder probabilities over all nonunit core divisors under this same complete-survivor law. Therefore every later original layout satisfies

\[
 E_\mu N_e\le R_0:=\frac{1301}{1185}.
 \tag{FE5}
\]

This uses one original class per numerical modulus \(3^ea\), and retains all four-prime cofactor supports and all permitted depths. No choice of later ternary prefixes changes the bound.

Put \(T_H=(1-3^{1-H})/2\). For \(H\ge2\), let \(h=(\sum_{e=2}^H3^{1-e}N_e)/T_H\); for \(H=1\), put \(h=0\). Then \(E_\mu h\le R_0\), since the late normalized load is a convex combination of the layers in (FE5). Following the integer selector in [report454](454-integer-first-layer-loads-give-core-margins-with-one-bounded-prime-height.md), set

\[
 \psi=g+h+1_{g>0},\qquad
 A:=\frac{2066}{1191}+\frac{1301}{1185}
   =\frac{444189}{156815}<3.
 \tag{FE6}
\]

Equation (FE4) gives \(E_\mu\psi\le A\). Choose one actual \(x\in S\) with \(\psi(x)\le A\). The nonnegative integer \(g(x)\) is at most one, since \(g\ge2\) implies \(\psi\ge3\). At that same point, using \(0\le T_H<1/2\),

\[
 2\ell_H(x)=2g(x)+2T_Hh(x)
 \le 2g(x)+h(x)=\psi(x)\le A.
 \tag{FE7}
\]

This proves (FE1), in particular \(\min_S\ell_H<B_H\), at arbitrary ternary and core heights. It excludes a failure of this corepoint route in the stated fixed early-phase family, including \(H\ge6\) and all \(h_5\ge4,h_7\ge3,h_{11}\ge2,h_{13}\ge2\), outside report454's four height strips.

## A good set with bounded Haar density

Let \(\lambda\) be uniform Haar probability on the complete core period \(\mathbb Z/Q\mathbb Z\). Since \(Q=(\prod_qw_q)\prod_q(q-1+u_q)\), one has

\[
 \lambda(S)=\frac{D(u)}{\prod_q(q-1+u_q)}\ge\frac{1191}{2880}
 =\frac{397}{960}.
 \tag{FE8}
\]

Indeed, the coefficients of \(2880D(u)-1191\prod_q(q-1+u_q)\), in the same mask order, are

```text
[0,493200,217440,139320,74592,69768,34992,17388,
 51120,55260,27240,14010,11736,7254,3876,1689].
```

Set \(m=(3-A)/2=13128/156815\) and \(G=\{x\in S:\psi(x)\le3-m\}\). Nonnegativity of \(\psi\) and (FE6) give

\[
 \mu(G)\ge1-\frac{A}{3-m}
 =\frac{4376}{152439},\qquad
 \lambda(G)\ge\frac{217159}{18292680}.
 \tag{FE9}
\]

Every point in \(G\) again has \(g\le1\), so (FE7) gives

\[
 \ell_H\le\frac32-\frac{6564}{156815}\quad\hbox{on }G.
 \tag{FE10}
\]

Thus the single probability \(\rho=\lambda(\,\cdot\mid G)\) is supported on the actual complete old residual, retains a positive original weighted completion margin, and satisfies the height-independent bound

\[
 \frac{d\rho}{d\lambda}\le\frac{18292680}{217159}.
 \tag{FE11}
\]

The set \(G\) is allowed to depend on the actual later original phases. The constants do not. These conclusions provide the good-core-set input to a tail theorem requiring positive mass and bounded Haar density; they do not by themselves enlarge an established global noncoverage range.

## Composition with the tail law

Apply [the positive-mass tail theorem](455-positive-mass-core-margins-give-height-independent-tail-cutoffs.md) with the uniform law on the good set \(G\), not the Dirac law obtained from (FE1). Its Haar density is below the valid rounded cap \(\Lambda=85\). For this fixed core prime set, its original head moments satisfy

\[
 J_1(Q)\le M_1=\frac{1001}{576},\qquad
 J_2(Q)\le M_2=\frac{7007}{1440},\qquad
 \left\lceil85M_2\right\rceil
 =\left\lceil\frac{119119}{288}\right\rceil=414.
 \tag{FE12}
\]

Consequently, if every outside prime is at least

\[
 B\ge3^{256}\,414^3,
 \tag{FE13}
\]

the tail theorem constructs one probability on the complete 3-free CRT product that avoids every original 3-free class. Its core marginal remains supported on \(G\), and its weighted completion load over all original labels having nonempty outside support obeys

\[
 L_{\mathrm{tail}}\le\frac{324\cdot85M_1}{B}
 =\frac{765765}{16B}<3^{-250}<\frac{6564}{156815}.
 \tag{FE14}
\]

Outside supports and all finite original exponent heights, including the whole family's ternary height \(H\), are unrestricted. There is still at most one original class per numerical modulus, and the tail theorem includes the unit core cofactor. The core marginal may change during the single global conditioning; (FE10) remains valid because it is pointwise on its preserved support \(G\). Thus the same final law has total weighted completion below \(3/2\), hence below \(B_H\). The cutoff (FE13) is independent of every core height. This is the original weighted completion interface; the established stronger global noncoverage results are unchanged.

## Exact arithmetic control and boundary

The [producer](../../frontier/cover-geometry/fixed_early_phase_core_margin.py) and [exact data](../../frontier/cover-geometry/fixed_early_phase_core_margin.json) retain the coefficient certificate and original arithmetic control. The producer reuses the constants in `k5_three_color_ap_control.py`, reconstructs both coefficient certificates, and materializes the fixed pattern family at heights \((4,3,2,2)\). This has 179 old and 179 first-layer original numerical moduli, all distinct, with CRT residues checked individually. A separate count decodes only those literal modulus/residue pairs and partitions all individual prime-power residues by their complete modular membership signatures. Its \(13\cdot16\cdot15\cdot15=46800\) cells give

\[
 |S|=1821723476,\qquad
 E_\mu g=\frac{1977830909}{1821723476}>1,\qquad
 E_\mu g+\Pr_\mu(g>0)=\frac{1570947623}{910861738}.
\]

Thus the outside-strip control has a first-layer mean exceeding one; the argument still gives an actual minimum below the completion threshold. The all-height and arbitrary-later-phase assertions follow from (FE4)--(FE7), not from this finite control. The coefficient and literal-original controls pass with `python3 -I -S -B -O`; they reconstruct the given fixed family and check both coefficient inequalities and the rounded-cap tail integer in (FE12). The literal membership count does not consult the pattern tables after the numerical originals have been materialized. Import alone produces no output. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fixed_early_phase_core_margin.py
```

The default output is exact JSON on stdout; `--output PATH` selects a file. The producer imports Chapter20's existing pattern constants from the sibling source rather than maintaining another copy.

An unresolved step even for this four-prime core is whether arbitrary old and arbitrary first-layer cofactor phases can force \(\min_S\ell_H\ge B_H\) beyond report454's height regions. The fixed-phase coefficient certificate does not answer that question. Arbitrary core prime supports also remain outside the good-core theorems used here; unrestricted Erdős #7 is not settled.
