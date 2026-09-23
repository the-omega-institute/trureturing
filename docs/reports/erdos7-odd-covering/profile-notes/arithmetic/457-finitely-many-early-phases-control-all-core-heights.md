# A finite early-phase frontier retains an all-height core margin

Only 57 numerical core cofactors need their old and first-layer phases prescribed. Let \(P=\{5,7,11,13\}\), \(Q=\prod_{q\in P}q^{h_q}\), with arbitrary finite positive heights, and let the whole original family have arbitrary finite ternary height \(H\ge1\). For each numerical modulus \(3^e a\), \(a\mid Q\), \(a>1\), \(0\le e\le H\), permit at most one original class, and permit missing classes.

For every **present** old class modulo \(a\le6125\), require the Chapter20 old cofactor phase. For every **present** first-layer class modulo \(3a\), \(a\le6125\), require its Chapter20 new cofactor phase; its residue modulo 3 is unrestricted. All old and first-layer phases at cofactors \(a>6125\) are arbitrary. Every original phase at \(e\ge2\) is arbitrary.

Then the actual complete old survivor set contains a set \(A\) such that

\[
 \lambda(A)>\frac1{100},\qquad
 \ell_H(x)\le\frac32-\frac1{50}=\frac{37}{25}
 \quad(x\in A),
 \tag{FF1}
\]

where \(\lambda\) is full core Haar probability and \(\ell_H\) is the original completion load. Thus \(\lambda(\,\cdot\mid A)\) has Haar density below 100, uniformly in every original height. The 57-cofactor frontier imposes at most 114 phase restrictions; this is not a claim of minimality among arbitrary or asymmetric frontiers.

The result consumes [report456](456-a-fixed-original-phase-family-has-core-margins-at-all-heights.md)'s actual fixed-phase margin. Reciprocal-tail and original-cylinder loss accounting are already supplied by [report302](../257-320/302-a-positive-actual-source-neighborhood-keeps-j-below403.md), [report326](../321-384/326-finite-original-label-tests-preserve-the-explicit-aligned-source-guard.md), and [Chapter56](../../problem-details/56-exponent-frontiers-and-cylinder-cover-certificates.md). The conclusion here is their concrete finite-frontier application, not a new general continuity theorem, Lean certification, or global noncoverage range.

## The reference law and actual original labels

Use exactly the Chapter20 support patterns and literal CRT interpretation in report456, FE2. Construct an auxiliary reference family on the **same complete period** \(Q\): every reference old and first-layer cofactor label has its prescribed pattern, at every permitted depth. Keep every actual original label at \(e\ge2\) unchanged. Reference first-layer ternary phases do not affect cofactor loads.

Let \(\bar S\) be the complete reference old survivor set and let \(\bar\mu=\lambda(\,\cdot\mid\bar S)\). This is an auxiliary reference law; it is **not** the uniform law on the actual perturbed survivor set \(S\). All subsequent sets remain on the same Haar carrier. The actual later phase family is fixed input to the construction, not selected afterward to suit a test.

Write \(\bar g\) for the full reference first-layer cofactor count. For each actual later exponent let

\[
 N_e(x)=\sum_{\text{present }3^e a,\ a>1}
          1_{x\equiv\alpha_{3^ea}\ (\mathrm{mod}\ a)}.
\]

Put \(T_H=(1-3^{1-H})/2\), and let \(h=T_H^{-1}\sum_{e=2}^H3^{1-e}N_e\) when \(H\ge2\), with \(h=0\) when \(H=1\). Report456, FE4--FE8, gives under this single reference law

\[
 \bar\psi=\bar g+h+1_{\bar g>0},\qquad
 E_{\bar\mu}\bar\psi\le c:=\frac{444189}{156815},\qquad
 \lambda(\bar S)\ge\frac{397}{960}.
 \tag{FF2}
\]

In particular the arbitrary later original events in \(h\) use the same \(\bar\mu\) as \(\bar g\). Pure powers of 3, corresponding to the unit cofactor, are excluded from this completion load and remain accounted for by \(B_H=(3+3^{1-H})/2\).

Take \(t=74/25=3-2/50\) and define \(A_0=\{x\in\bar S:\bar\psi(x)\le t\}\). Nonnegativity and (FF2) imply

\[
 \lambda(A_0)\ge\frac{397}{960}\left(1-\frac ct\right)
 =:c_0=\frac{99917}{5612160}.
 \tag{FF3}
\]

On \(A_0\), the integer \(\bar g\) is at most one, and hence
\(\bar g+T_Hh\le\bar\psi/2\le37/25\). This also includes \(H=1\).

## Pay only actual changed cylinders

Let \(D_0\) and \(D_1\) be the cofactors of present actual old and first-layer classes whose cofactor residue differs from its reference pattern. Missing original labels have no cost. Changing only the ternary residue at \(e=1\) also has no cost. Put

\[
 W_j=\sum_{a\in D_j}\frac1a\qquad(j=0,1).
 \tag{FF4}
\]

For each changed present label take its **actual new** cofactor cylinder, and let \(U_j\) be their union at layer \(j\). Each has full Haar mass exactly \(1/a\), so \(\lambda(U_j)\le W_j\). At the first layer this is \(1/a\), not \(1/(3a)\), since the completion event projects away the ternary coordinate.

Define \(A=A_0\setminus(U_0\cup U_1)\). Then

\[
 \lambda(A)\ge c_0-W_0-W_1.
 \tag{FF5}
\]

Every point of \(A\) avoids every actual old class: unchanged classes were already avoided by \(\bar S\), changed present classes are excluded by \(U_0\), and absent classes impose nothing. Its actual first-layer count is at most \(\bar g\), because changed present first-layer cylinders have been excluded by \(U_1\), while all remaining actual labels occur in the full reference inventory. Therefore its **actual** load satisfies

\[
 \ell_H=g_{\rm actual}+T_Hh
 \le\bar g+T_Hh\le\frac{37}{25}.
 \tag{FF6}
\]

This proves the quantitative perturbation version: any original early-phase changes with \(W_0+W_1<c_0\) retain positive Haar mass and the margin in (FF6). No symmetric-difference fee for the deleted reference cylinders is needed. The final law is the one actual probability \(\lambda(\,\cdot\mid A)\), supported on the actual residual.

## The 57-cofactor frontier and complete tails

Let \(\mathcal F\) contain all nonunit \(P\)-smooth integers at most 6125. Exact enumeration gives \(|\mathcal F|=57\). For cofactors outside it, the complete all-height reciprocal sum is

\[
 \begin{aligned}
 R_{6125}
 &=\prod_{q\in P}\frac q{q-1}
   -\sum_{\substack{a\le6125\\a\ P\text{-smooth}}}\frac1a\\
 &=\frac{1001}{576}
   -\sum_{a\in\mathcal F\cup\{1\}}\frac1a
 =\frac{48136815122003}{12637837812600000}.
 \end{aligned}
 \tag{FF7}
\]

Original numerical distinctness gives \(W_j\le R_{6125}\) separately at each of the two early layers, regardless of the actual finite heights or phases. Substituting into (FF5) gives

\[
 \lambda(A)\ge c_0-2R_{6125}
 =\frac{752533150011826549}{73880799852459600000}
 =\frac1{100}
  +\frac{13725151487230549}{73880799852459600000}.
 \tag{FF8}
\]

This proves (FF1). Only present cofactors dividing the actual \(Q\) impose constraints. The 57 fixed cofactors have coordinate exponents at most \((5,4,3,3)\); all other cofactors in that box and all cofactors outside it are free. Entire original exponent heights remain unchanged.

For comparison, fixing both early patterns throughout the box \((4,3,2,2)\) retains 179 nonunit cofactors and also certifies the same mass and margin; the uniform depth-three box retains 255. The box \((3,2,2,2)\), with 107 cofactors, does not satisfy this particular \(1/100\) mass budget. This is a comparison of sufficient reciprocal-tail payments, not an obstruction to that box's actual arithmetic. The preceding numerical cutoff 5929 also fails the chosen mass budget; 6125 is the first numerical-prefix cutoff certified by the symmetric payment \(2R\) at these fixed target constants.

## One weighted law after adding arbitrary outside supports

Apply [report455](455-positive-mass-core-margins-give-height-independent-tail-cutoffs.md) to \(\lambda(\,\cdot\mid A)\), using the valid density cap \(\Lambda=100\). The original head moments satisfy

\[
 J_1(Q)\le\frac{1001}{576},\qquad
 J_2(Q)\le\frac{7007}{1440},\qquad
 N\le\left\lceil100\frac{7007}{1440}\right\rceil=487.
 \tag{FF9}
\]

Thus all outside primes may have arbitrary finite supports, arbitrary original residues, and arbitrary finite exponent heights provided they are at least

\[
 B\ge3^{256}\,487^3.
 \tag{FF10}
\]

The resulting one law avoids every original 3-free class, keeps its core marginal supported on \(A\), and has original weighted tail completion at most

\[
 L_{\rm tail}\le\frac{225225}{4B}<3^{-250}<\frac1{50}.
 \tag{FF11}
\]

The complete family has the same arbitrary finite \(H\) throughout; it has not been truncated at any ternary depth. The tail includes the unit core cofactor. The marginal may change during global conditioning, but its pointwise core bound (FF6) survives, so total weighted completion is below \(3/2<B_H\). These are the original weighted completion and density conclusions; stronger established bare noncoverage ranges are unchanged.

## Exact original arithmetic control

The [program](../../frontier/cover-geometry/finite_early_phase_frontier.py) reads the existing report456 JSON constants and imports only Chapter20's pattern provider. Its [exact data](../../frontier/cover-geometry/finite_early_phase_frontier.json) retain the 57 cofactors, complete reciprocal payments, box comparisons, and all actual original labels of a separate control.

That control has core heights \((4,3,2,2)\), \(Q=4383754375\), and whole-family ternary height \(H=6\). It changes 126 old phases and 126 first-layer cofactor phases, all at cofactors greater than 6125. It omits the shallow original moduli 5 and 21. Later cofactor phases at \(e=2,3,4,5,6\) are respectively \(0,2,3,4,0\), each interpreted modulo its own cofactor; ternary phases are retained as actual CRT residues. All 1,251 numerical original moduli are distinct.

A count from literal modular membership signatures, without consulting the digit-pattern table during that count, checks 314,600 product cells. It finds 1,821,723,476 reference survivors and 2,399,232,038 actual survivors. The reference good set has 1,284,750,670 residues; excluding the actual changed cylinders leaves 1,283,433,848 residues in \(A\). The maximum actual completion load on this entire set is \(358/243<37/25\), checked again at a literal CRT witness. The changed first-layer phases increase the raw first-layer count on reference-good points of total Haar mass \(1228874/Q>0\), so the control exercises a real load increase as well as old-set deletion.

The optimized-mode control checks original CRT residues, numerical uniqueness, present shallow phase equality, missing shallow labels, both directed losses, the actual pointwise bound, and the exact exported constants. From the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite_early_phase_frontier.py
```

Output defaults to JSON on stdout; `--output PATH` selects a file. The finite control verifies one changed family. All-phase quantification outside the finite frontier and all-height quantification come from (FF2)--(FF8), not from this example. Arbitrary shallow cofactor phases, arbitrary core prime supports, and unrestricted Erdős #7 remain outside the conclusion.

[Report458](458-distinguished-prime-completion-removes-the-early-phase-restriction.md) gives a different weighted completion interface with arbitrary original phases, by choosing a distinguished prime at least 13 and the old core 3,5,7,11. That change of decomposition does not remove the shallow phase hypotheses from the ternary functional proved here.
