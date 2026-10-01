# 802: A same-source leakage budget permits positive selected-phase intersections

The fixed law and reference core of [Report801](801-retained-core-intersections-reduce-shallow-phase-contracts-to23-labels.md) admit positive actual leakage at selected numerical labels. Let

$$
\alpha_0=\frac{16790988780569}{557509082130000},\qquad
w=(3/16,3/16,5/24,5/24,5/24),
$$

and keep Report801's selected set

$$
F=\{15,21,45,33,35,39,63,51,57,55,105,75,69,65,99,77,85,117,95,165,91,147,225\}.
$$

The original family remains finite, with odd nonunit, numerically distinct moduli. Its prime support is contained in $\{3,5,7,11,13,17,19,23,29\}$ and an arbitrary finite set of primes strictly above3000. The omitted intermediate primes remain outside this result. The common affine normalization, actual pure-q survivor laws, weighted ternary law, core $G$, and inherited prime-tail analytic premise are exactly those of Report801. The derivation below is ordinary mathematics with exact rational checks, not Lean verification.

## 1. The same-source repair

For each selected label present in the actual family, let $A_m$ be its one actual cylinder after the common normalization; put $A_m=\varnothing$ if absent. Define one actual selected union and its leakage by

$$
E_F=\bigcup_{m\in F}A_m,\qquad
\ell=\lambda(G\cap E_F).
\tag{L1}
$$

All intersections in this definition use the same original product probability law $\lambda$, including its fixed five-leaf weights and actual pure-q inventories. No per-slot conditioning or reoptimization is performed.

Let $R$ be the union of the remaining old-head originals already charged in801. Its nonnegative residual-inventory argument gives

$$
\lambda(G)-\lambda(G\cap R)\ge L_F(t)\ge\alpha_0.
$$

Consequently the actual old-head survivor $U$ satisfies

$$
\lambda(U)\ge\lambda(G\setminus(R\cup E_F))
\ge L_F(t)-\ell\ge\alpha_0-\ell.
\tag{L2}
$$

Overlaps between the selected union and the already charged deletions only make this subtraction conservative. In particular any certified scalar $\varepsilon\ge\ell$ supplies the lower bound $\alpha_0-\varepsilon$. The directly checkable sufficient budget

$$
\sum_{m\in F}\lambda(G\cap A_m)\le\varepsilon
\tag{L3}
$$

is valid, but exact union leakage can be smaller than this sum. Neither formulation assumes independent selected cylinders or simultaneous maximization of their caps.

The128-vertex proof from801 is used unchanged before this subtraction. It is not necessary to assume that an arbitrary phase-dependent leakage formula is concave on that box. If the actual hit vector is known, the stronger condition $L_F(t)-\ell>\gamma$ can instead be evaluated at that same actual vector; here $\gamma$ denotes the source-mass gate defined next.

## 2. Exact leakage capacity of the retained continuation

Write $H_h=\mathbb E(Z-h)_+$ for the complete comparison-law hinge in801, and

$$
K=\left(1+15\frac58+216\frac5{24}\right)
\prod_{q\in\{5,7,11,13,17,19,23\}}
\left(1+\frac{q-1}{q-2}A_4(q)\right)
\left(1+\frac{28}{27}A_4(29)\right),
$$

$$
A_4(p)=\frac{15}{p-1}+\frac{50}{(p-1)^2}
       +\frac{60}{(p-1)^3}+\frac{24}{(p-1)^4},
$$

$$
\tau=\frac{21609}{10240}\left(\frac{99}{97}\right)^{21}
\frac{3000}{2999^4}
\sum_{j=0}^{21}\frac{21!}{(21-j)!21^j}.
$$

For any certified source mass $\alpha>0$, the complete29-plus-large-prime-tail lower bound is

$$
\mathcal R(\alpha)
=\max_{0\le h\le27}
\left[\frac{28-h}{27}-\frac{H_h+27K\tau}{27\alpha}\right].
\tag{L4}
$$

Thus this retained certificate is strictly positive exactly when

$$
\alpha>\gamma,
\qquad
\gamma=\min_{0\le h\le27}\frac{H_h+27K\tau}{28-h}
       =\frac{H_{16}+27K\tau}{12}
       =0.025677092080555696\ldots.
\tag{L5}
$$

The equality at16 is an exact comparison of all28 rational values. Noninteger thresholds provide no smaller gate: between consecutive integers the hinge is affine and the ratio inL5 is fractional linear, so an endpoint attains its minimum. Thresholds at least28 cannot produce positivity inL4.

The uniform budget is therefore

$$
\boxed{\quad
\ell<\Gamma:=\alpha_0-\frac{H_{16}+27K\tau}{12}
=0.004440782800366291\ldots.
\quad}
\tag{L6}
$$

EquationL6 defines an exact rational number; the accompanying JSON also retains its numerator and denominator. $\Gamma$ is a supremum for positive continuation using the uniform lower boundL2 and the fixed hinges/fourth-moment tail. At equality every corresponding boundL4 is nonpositive, with the16 threshold equal to zero. This is a certificate boundary, not a covering example, and it does not upper-bound the actual survivor mass. A different source estimate, actual hit vector, union computation, reference core or tail bound can permit larger leakage.

If the stronger final floor $3/50$ from801 must be retained, the admissible leakage supremum decreases to

$$
\alpha_0-
\min_{28-h>27(3/50)}
\frac{H_h+27K\tau}{28-h-27(3/50)}
=0.00043337536582869693\ldots.
$$

Only positivity is needed for the following strict extension.

## 3. One globally fixed positive-leakage instance

Choose no actual pure-q originals for $q\in Q$, so every $\lambda_q$ is Haar. Include the actual classes $0\bmod3$ and $1\bmod9$. Give every selected label exactly one fixed phase as follows; each pair is $(\text{modulus},\text{phase})$:

```
(15,7), (21,2), (45,22), (33,2), (35,2), (39,2),
(63,2), (51,2), (57,2), (55,2), (105,37), (75,52),
(69,2), (65,2), (99,2), (77,2), (85,2), (117,2),
(95,2), (165,112), (91,2), (147,100), (225,202).
```

All moduli are distinct. Every selected class except $100\bmod147$ has zero intersection with the one coreG. These zero statements are checked against the entire core event, not just against an independently selected forbidden class.

The exceptional class has ternary root1 and $x_7=2\bmod49$. The core then requires no5 hit and no hit among11,13,17,19,23: the allowed single non5 hit has already been used by7. Therefore its actual core intersection has mass

$$
\begin{aligned}
\ell
&=\frac38\frac1{49}\frac45
  \prod_{q\in\{11,13,17,19,23\}}\frac{q-1}{q}\\
&=\frac{20736}{4732273}
 =0.004381826661310537\ldots
 <\Gamma.
\end{aligned}
\tag{L7}
$$

Since only this selected event has positive measure, the selected union and the sum inL3 both equalL7 exactly. This family violates801's zero-intersection contract and satisfiesL6.

Its repaired uniform old-source mass is

$$
\alpha_0-\ell
=\frac{14348080620569}{557509082130000}.
$$

Using the same16 hinge gives a complete query bound of approximately27.584272377518733. After29 and the full tail above3000, the same-source distorted mass is

$$
\mathcal R(\alpha_0-\ell)
=0.0010181333297804777\ldots>\frac1{1000}.
\tag{L8}
$$

These finite25 originals resolve on the common period

$$
9\cdot25\cdot49\cdot11\cdot13\cdot17\cdot19\cdot23
=11712375675.
$$

The single integer9932944450 is4 mod9,2 mod49 and0 on the other displayed prime-power axes. It lies inG, hits the actual147 class, and avoids every other one of the25 actual classes. Thus the claimed positive leakage has a common CRT witness.

The integer10411000600 is4 mod9 and0 on every nonternary prime-power axis. It lies inG and avoids all25 actual classes. This is a witness for the displayed finite family only; it is not asserted to survive every extension.

The theorem also admits every finite extension by arbitrary phases at unselected old mixed labels, arbitrary old ternary heights at least3 including pure3 powers, and arbitrary29/allowed-large-prime originals, provided numerical distinctness and the stated support conditions hold and the old pure-q inventories remain empty. Such extensions may cover the displayed witness. They leave the chosen original product law andL7 unchanged, and all their deletions are already included in the complete inventories and continuation. Positive supported mass then supplies some survivor on the extension's full finite CRT carrier. No height cutoff is imposed.

For a limit control, replacing the225 phase by2 yields actual leakage $3456/676039=0.005112131104862293\ldots>\Gamma$ from that one slot. This does not prove coverage; it shows why positive leakage cannot be accepted without a budget check.

## 4. Reproducible exact checks and boundary

The [standalone consumer](../../../frontier/cover-geometry/refined-capped-source/same_source_leakage.py) reads the [declarative certificate](../../../frontier/cover-geometry/refined-capped-source/same_source_leakage_certificate.json) and compares its freshly computed output with the [retained exact result](../../../frontier/cover-geometry/refined-capped-source/same_source_leakage.json). The25 actual modulus/phase pairs, the CRT witnesses, the leakage budget and the control example are certificate data. The program checks odd nonunit and distinct moduli, canonical phases, the empty actual pure-q inventories, and one common3/9 normalization. Selected labels may be absent; they then contribute zero leakage.

The source premise is the specific previously verified [Report801 result](../../../frontier/cover-geometry/refined-capped-source/retained_core_phase_union.json), whose raw SHA256 is

```
dc4ceba98c8e992a85c001d50aed1928a255c937f4b1bc248b6f1850cb6e222c
```

The consumer requires that exact input identity before selecting its declared fixed-law case. It recomputes the28 continuation gates and all leakage-dependent arithmetic from the identified result. It does not reprove801's uniform source theorem or accept arbitrary source numbers as certified premises. The inherited ordinary analytic estimate and the absence of new Lean verification remain unchanged.

Each actual cylinder-core intersection is independently evaluated by enumerating the five leaves and128 first-digit hit patterns, retaining all declared prime-power depths through exact cylinder probabilities. The selected union is computed by exact CRT inclusion-exclusion, merging identical intersections and dropping cylinders of zero core mass. It is not silently replaced by an independent-product approximation or by the sum of its marginal masses. Both the actual union and the individual-intersection sum are retained. Every witness is checked against the entire core and the full finite actual family.

The default command, from the asset directory or using an explicit absolute script path, is

```sh
python3 -I -S -B same_source_leakage.py
```

It reads its certificate and result, and `retained_core_phase_union.json`, adjacent to the script. `--certificate`, `--source-result` and `--result` accept explicit paths; `--write-result <path>` regenerates a result instead of checking the retained one. No working-directory scan, package installation or optional Python dependency is used.

Normal and optimized executions each pass189 explicit checks, and default replay plus regeneration agree in an independent directory whose path contains spaces. Nine altered input kinds are rejected in both execution modes: a wrong positive-slot phase, an excessive budget, an underreported budget, a duplicate original modulus, an even original modulus, an unexpected pure-q original, a false common CRT witness, a changed inherited source artifact, and a forged retained result. Separate positive controls accept an absent zero-leakage selected slot and verify that two nested positive cylinders have joint mass strictly smaller than their individual-intersection sum. These controls verify the implementation; the conditional mathematical argument isL1–L8.

The mathematical improvement is a same-source quantitative interface: selected classes may meet the core if their one actual union is small enough. The bound does not remove arbitrary shallow-phase restrictions, permit separate per-slot sources, admit primes31 through3000, or resolve unrestricted Erdős#7.
