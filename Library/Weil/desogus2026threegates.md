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

The inspected primary version is [arXiv:2609.20367v2](https://arxiv.org/abs/2609.20367v2), submitted **20 September 2026**, 69 pages. The arXiv history still lists v2 as current at the 3 October inspection. Theorem 0.1 and Theorem 8.7 explicitly claim RH through positivity of the actual localized Weil operator on the real odd logarithmic channel. This is an all-zero claim, distinct from a proportion or fixed-window result. The full proof, external inputs and [supplementary certificates](https://doi.org/10.5281/zenodo.22864087) have not been independently verified here. No counterexample to the main proof was established by the bounded interface review either.

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

## A same-vector payment interface

The original square completion (209)–(212) retains two nonnegative arm squares. Write their sum as

$$
\mathcal S_k[F]=\sum_{\pm}
\|P_k^{1/2}t_\pm+P_k^{-1/2}b_kx_k\|^2.
$$

At the displayed coefficients, its exact accounting is

$$
\Phi_k=\mathfrak B_k|\gamma_k(f)|^2+\mathcal S_k[F]+Q_k-2D_k.
$$

Lemma 6.61 states the one-debit identity on the identified normalized vector $F_k^\#=H_kf_k^\natural$. Lemma 8.4 asserts the same identity on its general harmonic vector. Write $\mathcal C_k[F]=Q_k[F]-D_k[F]$. The displayed fold remainder is $\mathcal S_k[F]+\mathcal C_k[F]-D_k[F]$. Granting the source identification on the same $F$, it writes $\mathcal C_k=E_k(1-u_k)$ when $E_k>0$. The interface below uses $Q_k-D_k$ directly, so it remains meaningful at $E_k=0$ without dividing by $E_k$. This is a conditional accounting of the displayed form, not a verified transport identity for the actual Weil operator.

There is further coefficient slack in the source's parent-loss estimate. With $w_k=\log(1+1/k)$, put

$$
\mathcal L_k=\frac{439}{250}\sum_m\chi_m+\frac52W_k,
\qquad
\delta_k=-\log(kw_k)+\frac{439}{250}
\left(\frac{\sum_mV_{k,m}}{\log2}-\sum_m\chi_m\right).
$$

The coefficients in (203), (204) and MASTER-P3c give

$$
\mathfrak B_k-\mathcal L_k=\mathfrak g_k^{\rm M+}+\delta_k.
$$

The source bounds $0<kw_k<1$ and $\chi_m\le V_{k,m}/\log2$ make $\delta_k$ nonnegative. Nonnegative unused terms also arise from the two Young inequalities in Lemma 8.2 and from any excess of the exact inherited pivot over its certified floor. None of these sign statements supplies a comparison with the remaining $D_k$.

Throughout the proposed interface, $k$ is an integer at least seven, $A_{k,-}\succ0$, $f\in\mathcal K_k$, and $F=H_kf$ is the exact full-operator harmonic extension with the pole retained. Retain the order in Lemma 8.4: complete full-form transport, fixed-target gauge, simultaneous common-complement source short, then root-adapted endpoint fold. The one-defect and forcing identifications of Lemma 6.28, its positive multiplication coefficients, $1-\beta_kI_k>0$, $J_k>0$, $\Pi_k^{\rm phys}>0$, and the arm block $P_k\succ0$ must all hold in those coordinates. These correspondence and positive-pivot inputs remain unverified here; none is inferred from positivity of the future block.

A proposed unused remainder $\mathcal U_k$ is admissible only after establishing the common lower-form estimate

$$
\langle F,A_{k+1,-}F\rangle\ge
(\mathfrak g_k^{\rm M+}+\delta_k)|\gamma_k(f)|^2
+\mathcal R_k^\perp[f]+\mathcal S_k[F]+\mathcal U_k[F]
+Q_k[F]-2D_k[F].
$$

This lower bound is itself an unverified actual-family obligation. Conditional on it, a sufficient payment preserving the advertised ground coefficient and transverse reserve is

$$
D_k[F]\le\mathcal C_k[F]+\delta_k|\gamma_k(f)|^2
+\mathcal S_k[F]+\mathcal U_k[F]
\qquad\text{for every }f\in\mathcal K_k.
$$

Here $\mathcal U_k$ may contain only explicitly identified, proved nonnegative Young-residual or pivot-excess terms retained in that lower bound. Each must be disjoint from the expenditures already made in MASTER-P2 and the $3/5+2/5$ parent allocation, and from $\mathcal S_k$, the coefficient slack $\delta_k|\gamma_k(f)|^2$, and the transverse reserve $\mathcal R_k^\perp$ supplied by Theorems 6.53 and 6.55. It is not defined as the unknown difference. Taking $\mathcal U_k=0$ introduces no additional reserve; a nonzero choice needs the displayed lower-form proof. This interface is sufficient for the stated allocation scheme; positivity could also follow from a different allocation that spends part of the claimed ground margin. It is not asserted to be necessary for RH or for operator positivity.

The source reserves have distinct existing uses:

| Source input | Existing allocation | Additional obligation before using it for $D_k$ |
|---|---|---|
| Lemma 8.1, MASTER-P2 | Comparator saving and its negative reference charge are one inherited-response contribution. | Retain both terms; the saving is not an independent positive summand. |
| Lemma 8.2 | The certified inherited surplus is split $3/5+2/5$ to pay mixed and aligned forcing. | Identify the unused remainder and compare it with $D_k$ on the actual harmonic response. |
| Theorems 6.53 and 6.55 | The transverse budget supplies the reserved transverse term. | Prove any proposed reallocation while preserving the claimed transverse conclusion. |
| Lemma 8.4, (213) | One target diagonal splits into ground and transverse parts. | Keep the split and both expenditures in the same coordinates. |

The source does not identify an extra factor-of-two normalization in (209)–(213): the symmetric coupling is explicitly $\sqrt2\,b_k$, and the diagonal is retained once. No same-vector payment satisfying the interface above has been verified here. Harmonic restrictions could make the arm squares or parent remainders large enough; their quantitative consequence remains unverified. This narrows the reuse obligation without producing an actual-arithmetic counterexample or deciding the source's claimed RH conclusion. The coefficient calculation and conditional scalar accounting do not constitute new mathematical estimates.

The [v2 supplementary archive](https://doi.org/10.5281/zenodo.22864087), file `The_Three_Gates_Supplementary_V2.zip`, contains a Gate-II audit of full-comb scalarization. That audit explicitly limits its verdict to that particular risk and says it does not independently reprove every theorem. Its reported PASS therefore does not verify this second-arm payment. The archive describes its `master/` programs as finite scalar sweeps and its `Y7_end_to_end/` calculation as a conservative base-endpoint replication; those stated scopes do not supply the missing all-step, same-vector lower bound. These computations have not been rerun here.

## Full-form transport input

Proposition 5.3 must be read as an obligation about the whole form, including its diagonal. For a change of variables $x=\phi(u)$ with $J=\phi'>0$ and $g(u)=\sqrt{J(u)}f(\phi(u))$, substitution in the singular difference expression produces

$$
K(\phi(u),\phi(v))
\left|\sqrt{J(v)}g(u)-\sqrt{J(u)}g(v)\right|^2.
$$

Using only the transported off-diagonal kernel $\sqrt{J(u)J(v)}K(\phi(u),\phi(v))$ in an ordinary $|g(u)-g(v)|^2$ form leaves a multiplication term to account for, together with the transported endpoint potential. The exponential kernel identities in Lemma 5.1 do not by themselves perform this diagonal comparison. Before applying the later one-cell lower form, its full transported potential must be identified or bounded in the same coordinates. The bounded review has not completed the identification of the source's $c_A$ with all the later collar and fixed-target forms. No failure of the entire RH claim follows merely from this outstanding correspondence.

The source formulas give a specific normalization benchmark for this interface. Denote the archimedean form in (61), with the pole and prime terms excluded, by $\mathfrak a_{\mathrm{arch},a}$. For $a>0$, use the affine unitary

$$
(Tf)(t)=\sqrt2\,f(2t-1),\qquad 0<t<1.
$$

On the smooth compactly supported core, substitution in (12)–(15), (50) and (62) gives

$$
\mathfrak a_{\mathrm{arch},a}[T^{-1}g]
=\mathfrak b[g]+\bigl(c_0(a)-\log2\bigr)\|g\|_2^2
-\langle g,K_{\gamma,2a}^{(0,1)}g\rangle,
\qquad c_0(a)-\log2=-\log(4\pi a)-\gamma,
$$

where $K_{\gamma,2a}^{(0,1)}$ has kernel $2a\rho(2a|t-s|)$. The singular difference energy retains its coefficient, while

$$
V(2t-1)=-\log2-\frac12\log\bigl(t(1-t)\bigr).
$$

The original odd domain becomes $g(1-t)=-g(t)$. Extension of this core calculation requires the actual transported closed-form domain and common form-core contract. This affine map is not identified with the exponential $U_A$ or the paper's complete collar gauge. The benchmark states which scalar and regular-kernel terms occur before that identification; it neither supplies a new lower bound nor contradicts Proposition 5.3. Reusing the later $\mathfrak b$ estimates still requires the complete realization and allocation of these terms in the same direct/source forms. The displayed calculation is paper-level source bookkeeping, without a Lean validation of the integral or domain transport.

There is also a benchmark in the actual parent-cell coordinate of §6.9. Transport the same archimedean formula by $R_a$ from (8), before odd restriction. Its physical gamma kernel is $\rho(|y-z|)$, and its multiplication coefficient is

$$
c_0(a)+V(y/a)=-\log(2\pi)-\gamma-\frac12\log(a^2-y^2).
$$

Write $\mathfrak h_J$ for the singular quarter difference form on an interval $J$. Let $I=(\ell,r)\subset(-a,a)$, $w=r-\ell$, $f\in C_c^\infty(I)$, and let $E_If$ be its zero extension. The exterior strips give

$$
\mathfrak h_{(-a,a)}[E_If]-\mathfrak h_I[f]
=\frac12\int_I\log\frac{a^2-y^2}{(y-\ell)(r-y)}|f(y)|^2\,dy.
$$

The physical endpoint potential is $-\tfrac12\log(a^2-y^2)$; it cancels the numerator in this strip contribution. With $g(u)=\sqrt w\,f(\ell+wu)$, the resulting compression is

$$
\mathfrak a_{\mathrm{arch},a}^{\mathrm{ph}}[E_If]
=\mathfrak b[g]-\bigl[\log(2\pi w)+\gamma\bigr]\|g\|_2^2
-\langle g,K_{\gamma,w}^{(0,1)}g\rangle,
\qquad K_{\gamma,w}^{(0,1)}(u,v)=w\rho(w|u-v|).
$$

For a Mellin parent $C_m=[m,m+1)$ within $[1,e^{2a}]$, use $t=e^{y+a}$. Its physical interval is $I_m=(\log m-a,\log(m+1)-a)$, with $w=w_m$. The coordinate $u=\log(t/m)/w_m$ is the one used in (103)–(104). This calculation is a compression, whereas Theorem 6.53 takes an infimum over a free common complement. For the same form, prescribed data and admissible complement, zero extension is only one competitor and gives an upper comparison for that infimum. The physical compression has not been identified with the theorem's short of $\mathfrak b$. A nonsymmetric single-parent test also needs its reflected component and all cross terms to become an odd test. The pole and prime terms are excluded from these archimedean benchmarks; no counterexample to the actual odd Weil form is asserted.

The remaining realization must specify its full potential, starting interval, preceding map from the odd physical space, and relation between $A$, $a$ and $w_m$. The displayed proof of Proposition 5.3 does not identify these data. Lemma 6.16 preserves the target ground line and its orthogonal splitting; that alone is not a transformed-potential identity. Lemma 6.51 and Theorem 6.53 calculate on the already-specified $\mathfrak b$, and Lemma 8.4 invokes Proposition 5.3 again. These source dependencies locate the missing correspondence without proving that no such correspondence can exist.

The [existing small-support spectral supplier](suzuki2026screw.md) and [localization account](frankliebseiringer2006hardy.md) already cover the corresponding basic boundary energy and its small-window use. They should be reused; neither supplies this paper's all-scale collar correspondence. The supplementary scalarization audit limits its PASS to the stated scalarization risk and does not independently establish the complete diagonal identification.

## Relation to the FIB research gap

The retained-old-block, mixed-coupling and Schur-induction architecture is standard and is explicitly attempted at all scales in this source. Naming the support schedule after Fibonacci therefore supplies no architectural novelty. The project's [exact block reduction](../../D5/S3/Weil/ZetaLinear/ExactStickyReduction.lean) and [golden positivity induction](../../D5/S3/Weil/TestFunctions/GoldenPositivityInduction.lean) remain reusable under their own assumptions; this review did not rebuild them.

For an actual finite positive old block $H$, the additional estimate is $B^*H^{-1}B\preceq D$ for the matching new block and coupling; a semidefinite old block also needs the appropriate range condition. This source's claimed budget bridges are relevant candidates for detailed comparison with that obligation. They are not adopted as a supplier that has already closed it. The local scalar audit does not settle the full comparison. No external certificates, prime or zero samples, or Lean declarations were produced for this review.
