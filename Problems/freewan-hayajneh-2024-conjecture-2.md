---
slug: freewan-hayajneh-2024-conjecture-2
bibkey: freewanhayajneh2024geometricmean
doi: 10.7153/mia-2024-27-15
url: https://files.ele-math.com/articles/mia-27-15.pdf
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation.result
---

# Freewan–Hayajneh: weighted geometric means and aggregate norm inequalities

## Problem

S. Freewan and M. Hayajneh, *On a conjecture related to the geometric mean and norm inequalities*,
*Mathematical Inequalities & Applications* 27 (2024), 193–200, DOI 10.7153/mia-2024-27-15,
Conjecture 2, printed p. 194. The authors attribute its first proposal to their LAA 670 (2023),
104–120 paper, DOI 10.1016/j.laa.2023.04.012; the 2024 paper restates it. See
[freewanhayajneh2024geometricmean](../Library/Eigenstructure/freewanhayajneh2024geometricmean.md).

> CONJECTURE 2. If A_i, B_i ∈ P_n for all i = 1, …, m, and t ∈ [0,1], then |||∑_{i=1}^m (A_i² #_t
> B_i²)^r||| ⩽ |||((∑A_i)^{(1−t)pr}(∑B_i)^{2tpr}(∑A_i)^{(1−t)pr})^{1/p}||| for all 2r ⩾ 1 and for
> all p > 0 and for all unitarily invariant norms.

The formal proposition retains every natural dimension $n$, every $m\ge1$, every pair of families
$A,B:\operatorname{Fin}(m)\to M_n(\mathbb C)$ whose members are positive definite, every
$t\in[0,1]$, every real $r$ with $1\le2r$, every $p>0$, and every unitarily invariant norm. The
weighted mean is $X\#_tY=X^{1/2}(X^{-1/2}YX^{-1/2})^tX^{1/2}$; powers use spectral functional
calculus. The additional $n=0$ case has only the zero matrix; every norm vanishes there, so its
inequality is trivial. No global nonemptiness instance restricts the dimension quantifier.

## Motivation

The source proves the case $t=1/2$, $r\ge1$ and $pr\ge1$. The conjecture would extend the comparison
to $r\ge1/2$ and remove the product restriction, uniformly over finite families and unitarily
invariant norms.

## Gap

The aggregate inputs can have a fixed scalar product while noncommutativity in the individual
geometric means produces a positive diagonal shift. Pairing each input with a sign conjugate removes
off-diagonal entries without removing that shift. Thus scalar control of the aggregate product does
not control the operator norm of the sum of square roots of the individual means.

## Route

Take $n=m=2$, $t=r=1/2$, $p=2$, and

$$
P=\begin{pmatrix}1&3/20\\3/20&9/4\end{pmatrix},\quad
Q=\begin{pmatrix}1&1/5\\1/5&4/9\end{pmatrix},\quad
J=\operatorname{diag}(1,-1).
$$

Use $(A_1,B_1)=(P,Q)$ and $(A_2,B_2)=(JPJ,JQJ)$. Positive leading principal minors give positive
definiteness: $\det P=891/400>0$ and $\det Q=91/225>0$. The sums are $A=\operatorname{diag}(2,9/2)$
and $B=\operatorname{diag}(2,8/9)$, so $AB=4I$ and the right matrix is $2I$.

For $z=1/100$, put

$$
X=97+135z-648z^2,\quad Y=97-385z-648z^2,\quad
R=9409-27504z+46656z^2,\quad u=\sqrt R,\quad
v=\sqrt{(1-z)(1-9z)}.
$$

The numerator

$$
N=\begin{pmatrix}X&312(1/10)(1-3z)\\312(1/10)(1-3z)&Y\end{pmatrix}
$$

is positive definite and satisfies $N(P^2)^{-1}N=RQ^2$, so Riccati uniqueness identifies
$C=P^2\#_{1/2}Q^2=N/u$. Since $\det C=v^2$, the positive square root is
$M=(C+vI)/\sqrt{\operatorname{tr}C+2v}$.

The exact rational estimates $C_{11}-1\ge11z/4$, $C_{12}^2<52z/5$, $\operatorname{tr}C\ge2$ and
$v\ge9/10$ give

$$
(M_{11}^2-1)(\operatorname{tr}C+2v)
=(C_{11}-1)(\operatorname{tr}C+2v)-C_{12}^2
>\frac{11z}{4}\frac{19}{5}-\frac{52z}{5}
=\frac z{20}>0.
$$

Thus $M_{11}>1$. Covariance under $J$ gives the left matrix $2\operatorname{diag}(M_{11},M_{22})$.

The uniform bounds in this dossier and the interval bounds used in Lean are two distinct
estimation routes. The displayed uniform bounds are paper results; the Lean proof uses
the fixed-instance bounds $1.028<C_{11}<1.029$, $0.973<C_{22}<0.974$ and $0.949<v<0.950$.

## Falsifier

The Euclidean operator norm is unitarily invariant. Its value on the right matrix is $2$, whereas
its value on the left is at least $2M_{11}>2$. This contradicts the asserted inequality at
admissible parameters $t=r=1/2$ and $p=2$. No floating-point estimate is needed.

## Evidence

`D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation.conjecture` states the complete
universal assertion, and `.result : ¬ conjecture` negates that exact proposition. The existing
weighted geometric mean and spectral matrix-power definitions supply the mathematical
operations. The scoped report exited 0, covering 16 modules and 796 declarations, including
the exact rational inputs, radical certificate and operator-norm comparison. The axiom
closure of `result` is `Classical.choice`, `Quot.sound`, `propext`. The shared SL-031
pre-freeze check passed, with `is_closed_negation=true` and literal compiled types `Prop`
and `Not conjecture`. This evidence has scoped coverage; full delta-rule, gate and required
checks are not established by it.

## Triage

**LEAN-PROVED — Conjecture 2 is false.** `result : ¬ conjecture` uses exactly
$n=m=2$, $t=r=1/2$, $p=2$ and $\varepsilon=1/10$. Its live proof checks positivity,
the Riccati certificate, the spectral square roots, the sign-conjugate sums, the right
matrix $2I$, and the strict operator-norm lower bound. The complete original quantifiers,
including $m\ge1$, remain in `conjecture`.

**PAPER-PROVED — Fixed aggregate product for every $p>0$.** The displayed sums obey
$AB=4I$. Since they are commuting positive diagonal matrices, each diagonal entry of
$A^{p/4}B^{p/2}A^{p/4}$ equals $2^p$, and its $1/p$ power equals $2$.
This all-$p$ calculation is an explanatory consequence; the Lean proof uses only $p=2$.

**PAPER-PROVED (literature) — Existing positive cases remain unaffected.** The source states
its proved range $t=1/2$, $r\ge1$, $pr\ge1$ on p. 194. The counterexample has $r=1/2$.
The paper's existing proof of Conjecture 1 is unaffected: this result concerns the different
assertion Conjecture 2 and lies outside that positive range.

**OPEN — The restriction $r\ge1$ without the product restriction.** Neither this
counterexample nor the cited positive case decides all $r\ge1$ and all $p>0$.

**PAPER-PROVED — New Conjecture 3 counterexample at $s=2$.** In the source statements,
Conjecture 2 is exactly Conjecture 3 specialized to $s=2$. Thus these inputs supply a new
$s=2$ counterexample to Conjecture 3. The separate reported MI-21 refutation uses $s=1/2$;
that different specialization does not imply the present result. The statement correspondence
and literature attribution are not separate Lean theorems in this module.

**NUMERICALLY-COMPUTED — Finite evaluations.** The left operator norms are approximately
$2.0024304066$, $2.000653$, and $2.0000267$ at
$\varepsilon=1/10,1/20,1/100$, respectively. These are floating-point readings,
not kernel evidence and not a proof of a parameter family.

**PAPER-PROVED — Direct-sum extension to every $n\ge2$.** Replacing each input by its
direct sum with $I_{n-2}$ for $n\ge2$ preserves positive definiteness. Blockwise functional calculus
adds
the same $2I_{n-2}$ block to both compared matrices for $t=r=1/2$, every member of the
parameter family below and every $p>0$. The first block still has norm greater than $2$,
and the operator norm of a block diagonal matrix
is the maximum of the block norms. This extension is not formalized in this module.

**PAPER-PROVED — Parameter family $0<\varepsilon\le1/10$, all $p>0$.** Replace the
off-diagonal entries of $P,Q$ by $3\varepsilon/2,2\varepsilon$, respectively, retaining
the sign-conjugate pairs and $t=r=1/2$. Put $z=\varepsilon^2$. The determinants are
$9(1-z)/4>0$ and $4(1-9z)/9>0$, so all inputs remain positive definite. The aggregate
matrices are unchanged, hence the right matrix equals $2I$ for every $p>0$.

With $X,Y,R,u,v$ as in Route, now at $0<z\le1/100$, the numerator $N$ has off-diagonal
entry $312\varepsilon(1-3z)$. The polynomial identities
$N(P^2)^{-1}N=RQ^2$ and $\det N=(1-z)(1-9z)R>0$, together with $N_{11}=X>0$,
identify the same positive Riccati solution $C=N/u$. The uniform bounds in Route follow from

$$
\begin{aligned}
(97-140z)^2-R&=z(344-27056z)>0,\\
X-(1+11z/4)(97-140z)&=z(33/4-263z)>0,\\
R-9409(1-3z)^2&=z(28950-38025z)>0,\\
(X+Y)^2-4R&=4z(3254-156743z+162000z^2+419904z^3)>0.
\end{aligned}
$$

All denominators are positive on this interval; $97344/9409<52/5$ gives the bound for
$C_{12}^2$, and $v^2=(1-z)(1-9z)\ge9009/10000>81/100$ gives $v\ge9/10$.
The square-root identity in Route therefore yields $M_{11}>1$ throughout the interval,
so the left operator norm exceeds $2$ for every $p>0$. This family is not formalized in
this module; its Lean proof checks only $\varepsilon=1/10$ and $p=2$.

## ASSUMED-UNVERIFIED

Literature status: no settlement of Conjecture 2 found in the searched scope;
no worldwide priority is claimed. The scope includes Ando–Hiai and Araki comparison results
as stated in Dinh–Ahsani–Tam (2016), including the obstruction to passing termwise
log-majorization through matrix sums. It does not establish exhaustive coverage of the
original Ando–Hiai article or subsequent literature. The reported MI-21 result concerns
Conjecture 3 at $s=1/2$, rather than the $s=2$ specialization addressed here.
