---
bibkey: desogus2026threegates
authors: Marco Desogus
year: 2026
title: "The Three Gates: A Rooted-Operator Approach to Weil Positivity"
doi: null
url: https://arxiv.org/abs/2609.20367v2
claim: The preprint claims all-scale odd-channel Weil positivity via a common-cut Schur induction; this note records its actual-operator proof interfaces without adopting its claimed RH proof as a verified input.
strata_touched: []
license: citation-only
triage: anchor
---

# Common-cut Schur induction: an unadopted all-scale claim

The inspected primary version is [arXiv:2609.20367v2](https://arxiv.org/abs/2609.20367v2), submitted **20 September 2026**, 69 pages. The arXiv history still lists v2 as current at the 1 October inspection. Theorem 0.1 and Theorem 8.7 explicitly claim RH through positivity of the actual localized Weil operator on the real odd logarithmic channel. This is an all-zero claim, distinct from a proportion or fixed-window result. The full proof, external inputs and [supplementary certificates](https://doi.org/10.5281/zenodo.22864087) have not been independently verified here. No counterexample to the main proof was established by the bounded interface review either.

## The actual induction step

At the arithmetic endpoint $a_k=(\log k)/2$, the source retains the pole term in $A_k=C_k-2|s_k\rangle\langle s_k|$. Lemma 6.27, under the old endpoint's positivity and inverse hypotheses, forms the actual harmonic extension

$$
H_k f=\binom{-A_k^{-1}B_{A,k}f}{f},\qquad
B_{A,k}=B_k-2s_kt_k^*,\qquad T_k=H_k^*A_{k+1}H_k.
$$

Theorem 8.5, printed pp.58–59, claims for every integer $k\ge7$, assuming $A_{k,-}>0$, a lower bound on this same extension by a strictly positive ground-coordinate coefficient plus a nonnegative transverse remainder, strictly positive when the transverse component is nonzero. This is the claimed estimate yielding $T_k>0$. The old-block positivity is an induction hypothesis, not an assumption of all-scale positivity. Theorem 1.2's restricted odd Weil criterion and the endpoint-to-all-support closure are separate consumers of the induction.

The load-bearing comparisons to inspect before any reuse are:

- Theorem 6.53 and Theorem 6.55: simultaneous ground/transverse budgets on the same common complement and the required transverse reserve.
- Lemma 8.1: placement of the full actual Schur response, with its positive saving and negative reference charge attached to the same contribution.
- Lemma 8.2: the homogeneous mixed and aligned-forcing estimate for all complex coefficients, not only a normalized scalar case.
- Lemma 8.4: the common-cut, transported form and endpoint-fold identities for the same harmonic vector, including the pole term, actual forcing and physical-pivot positivity.
- Certificate 6.62 and Certificate 8.3: the base at $Y=7$ and the all-$k$ ground margin, whose stated finite interval verification is paired with an analytic tail.

These are propositions that the source claims to prove. They are not merely extra conjectural hypotheses declared by its author; they also have not become independently verified project premises by being listed here. Checking scalar certificates alone would leave the actual-operator and function-space correspondence obligations untouched.

## Debit multiplicity and physical-pivot inputs

The displayed local formulas require a specific reconciliation before they can supply an all-scale estimate. In Lemma 8.4, equations (207)–(212) give two endpoint arms with the same positive target block $P$ and coupling $b$. Completing both squares deducts

$$
2D=2\|P^{-1/2}bx\|^2.
$$

Equation (212) explicitly calls $D=|\widehat h_0|^2/\Pi^{\rm phys}$ the **one-arm** debit. In contrast, (205) and MASTER-P3b use the once-deducted remainder $Q-D=E(1-u)$. At these displayed coefficients, that remainder alone does not bound the two-arm remainder. A reuse must identify the additional payment, or an explicit normalization or allocation that reconciles the same $Q$, $D$ and direct target diagonal. An overall change of units must transport all three together.

A scalar check isolates this issue without claiming to realize an arithmetic endpoint. In the one-defect model of Lemma 6.28, take both pieces to have measure one, $a_-=a_+=1$, $\beta=1/4$, $x_-=1/3$, $x_+=1$. Then the left pivot is $3/4>0$, $\gamma^c=1/3$, $g_-=0$, $h=\Pi^{\rm phys}=2/3>0$, and

$$
Q=D=\frac23,\qquad Q-D=0,\qquad Q-2D=-\frac23.
$$

Equivalently, the two displayed positive arm blocks $P=2/3$ and couplings $b=2/3$, minimized at $t_+=t_-=-1$, give $-2/3$ after subtracting the separately retained target diagonal. These are exact rational values. The example shows that the once-deducted estimate is insufficient for those local displayed formulas; it is **not** a counterexample to the actual Weil operator, nor does it show that all the other reserves in the complete argument fail.

The sign needed for the physical pivot is a separate input. With the notation of (124)–(135), positive $|R|,J$ and $1-\beta I>0$ give

$$
\Pi^{\rm phys}
=\frac{|R|}{J}\frac{1-\beta(I+J)}{1-\beta I}.
$$

Thus the old left-block condition alone does not supply the numerator's positivity. The algebra in Lemma 6.28 is valid under its stated positive-pivot condition; the relation $g=A^{\rm pre}x$ transports the forcing but does not establish that sign. The actual compression/shorting map must identify this pivot as one whose positivity follows from the permitted induction inputs. The review has not completed that identification. This is an unclosed proof input, not a claim that an old-block induction hypothesis is inherently circular.

## Full-form transport input

Proposition 5.3 must be read as an obligation about the whole form, including its diagonal. For a change of variables $x=\phi(u)$ with $J=\phi'>0$ and $g(u)=\sqrt{J(u)}f(\phi(u))$, substitution in the singular difference expression produces

$$
K(\phi(u),\phi(v))
\left|\sqrt{J(v)}g(u)-\sqrt{J(u)}g(v)\right|^2.
$$

Using only the transported off-diagonal kernel $\sqrt{J(u)J(v)}K(\phi(u),\phi(v))$ in an ordinary $|g(u)-g(v)|^2$ form leaves a multiplication term to account for, together with the transported endpoint potential. The exponential kernel identities in Lemma 5.1 do not by themselves perform this diagonal comparison. Before applying the later one-cell lower form, its full transported potential must be identified or bounded in the same coordinates. The bounded review has not completed the identification of the source's $c_A$ with all the later collar and fixed-target forms. No failure of the entire RH claim follows merely from this outstanding correspondence.

## Relation to the FIB research gap

The retained-old-block, mixed-coupling and Schur-induction architecture is standard and is explicitly attempted at all scales in this source. Naming the support schedule after Fibonacci therefore supplies no architectural novelty. The project's [exact block reduction](../../D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean) and [golden positivity induction](../../D5/S3/Weil/TestFunctions/GoldenPositivityInduction.lean) remain reusable under their own assumptions; this review did not rebuild them.

For an actual finite positive old block $H$, the additional estimate is $B^*H^{-1}B\preceq D$ for the matching new block and coupling; a semidefinite old block also needs the appropriate range condition. This source's claimed budget bridges are relevant candidates for detailed comparison with that obligation. They are not adopted as a supplier that has already closed it. The local scalar audit does not settle the full comparison. No external certificates, prime or zero samples, or Lean declarations were produced for this review.
