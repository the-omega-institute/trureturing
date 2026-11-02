---
slug: ptaszynski-2022-unidirectional-skewness-minus-kurtosis-upper-bound
bibkey: ptaszynski2022skewness
doi: 10.1103/PhysRevE.106.024119
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.result
---

# The sharp upper bound on skewness minus kurtosis of a unidirectional unicyclic current

## Problem

K. Ptaszyński, *Bounds on skewness and kurtosis of steady-state currents*, Phys. Rev. E 106, 024119 (2022), arXiv:2204.08421v4, Section III E 1, `main.tex` line 432, gives

$$
\max(\mathcal S-\mathcal K)=B=\frac{3(107+51\sqrt{17})}{2048},
\qquad A=\frac{5-\sqrt{17}}4.
$$

Line 424 specifies the asymptotic family: the exceptional clockwise rate is $ak$, the other rates are $k$, and $a=A/N$ as $N\to\infty$. Appendix line 792 states that the extremal-topology assertion was numerically conjectured. Thus the analytic endpoint on the proposed topology is source input; its universal validity for arbitrary positive rate vectors needs proof.

**Source sign discrepancy.** The detailed display at line 432 and Figure 6 concern $\mathcal S-\mathcal K$, but the summary at line 133 prints $\mathcal K-\mathcal S\in[-0.15,0.465]$. The two signs conflict. This problem follows the detailed display and Figure 6; it does not identify the reversed-sign summary with that claim.

The exact reading is preregistered in [#25765](https://github.com/the-omega-institute/trureturing/issues/25765) and its [unchanged endpoint comment](https://github.com/the-omega-institute/trureturing/issues/25765#issuecomment-6585311119). For every natural $N\ge2$ and every $k:\mathrm{Fin}\,N\to\mathbb R$ with $k_i>0$ for all $i$, put

$$
R_j=\sum_{i:\mathrm{Fin}\,N}k_i^{-j},\qquad
\mathcal S(k)=\frac{3R_2^2}{R_1^4}-\frac{2R_3}{R_1^3},\qquad
\mathcal K(k)=\frac{15R_2^2}{R_1^4}-\frac{20R_3}{R_1^3}
+\frac{6R_4}{R_1^2R_2}.
$$

Define the set of actual admissible values

$$
V=\{s\in\mathbb R\mid \exists N\in\mathbb N,\ N\ge2\ \land\
\exists k:\mathrm{Fin}\,N\to\mathbb R,\ (\forall i,\ k_i>0)\ \land\
s=\mathcal S(k)-\mathcal K(k)\}.
$$

The proved claim is the conjunction of $\mathcal S(k)-\mathcal K(k)\le B$ for every such $N,k$ and $\operatorname{IsLUB}(V,B)$. Both ratios use the same vector, repeated rates retain their multiplicities, the coordinates are arbitrary positive reals, and $N$ is unbounded. The claim includes $N=2$ and assumes no extremal topology. Sharpness concerns this full actual-value set, not a finite prefix or a relaxation to independently chosen moments.

The source's $\mathcal S$ and $\mathcal K$ are third-to-first and fourth-to-second **scaled current-cumulant ratios** (`main.tex` lines 53–54), not standardized central moments. The inverse-rate formulas follow by substitution in the source's winding-number and waiting-time cumulant expressions (Appendix lines 772–775 and 787–790). Their original Lean definitions are `UnicyclicSkewnessMinimum.skewness` and `UnicyclicKurtosisLowerBound.kurtosis`. See [the source note](../Library/StatisticalMechanics/ptaszynski2022skewness.md).

## Motivation

The difference constrains the joint higher current cumulants of one positive unidirectional cycle. The universal inequality supplies a criterion for excluding this class from a measured pair of ratios when the current interpretation applies. The least-upper-bound clause shows that a smaller uniform constant cannot work over all finite cycle sizes. This exclusion alone does not exclude bidirectional unicyclic models or establish multicyclicity.

## Gap

The accepted bounded source/reuse screen reports `not-found-in-searched-scope` for an exact existing supplier of this universal endpoint together with actual positive-rate sharpness. Its scope includes the repository and original private suppliers, pinned Mathlib, the inspected eligible third-party Lean sources, and the inspected later arXiv sources. It is not an exhaustive theorem-equivalence or worldwide priority search. Repository matches for skewness, kurtosis, and their sum supply definitions and joint-moment estimates; they do not by themselves state this difference endpoint.

The source/reuse screen is inherited evidence, not a new literature search in this dossier. Its access, indexing and Lean-compatibility limits remain: the APS journal body, exact membership of all five OpenAlex citing records, and exhaustive theorem equivalence are unverified. Absence in these searched scopes establishes neither global openness nor original-proof priority. The primary-source anchors are the v4 TeX display and numerical-conjectural topology statement described above.

## Route

Unqualified helper names in this section belong to `UnicyclicSkewnessMinusKurtosisUpperBound`; they are private. The public theorem is `result : claim`.

1. **Reuse the common-vector normalization.** Put $x_i=k_i^{-1}/R_1$, $a=\sum_i x_i^2$, $b=\sum_i x_i^3$ and $c=\sum_i x_i^4$. The definitions `normalizedRates`, `p`, `q`, `r` and the theorem `normalized_moments` are the original suppliers in `UnicyclicSkewnessPlusKurtosisLowerBound`. The original normalization identities `UnicyclicSkewnessMinimum.skewness_normalized` and `UnicyclicKurtosisLowerBound.normalized` give, by `normalized_difference`,

   $$\mathcal S-\mathcal K=-12a^2+18b-6c/a.$$

   For $N\ge2$ and positive rates, the reused joint-moment theorem supplies $a>0$, $b\ge0$, $b^2\le ac$ and $c<a^2$. These facts all concern the same normalized vector. No separate optimizer for one moment is substituted into another.
2. **Bound the normalized expression.** Set $t=b/a$. The four inequalities give $t\ge0$, $t^2<a$ and $c/a\ge t^2$, hence

   $$\mathcal S-\mathcal K\le -12a^2+18at-6t^2.$$

   If $t\le3/4$, completing the square gives

   $$-12a^2+18at-6t^2=-12(a-3t/4)^2+3t^2/4\le27/64\le B.$$

   If $t>3/4$, put $f(t)=-12t^4+18t^3-6t^2$. Then

   $$f(t)-(-12a^2+18at-6t^2)=(a-t^2)[12(a+t^2)-18t]\ge0.$$

   For every $t\ge0$ the exact factorization

   $$B-f(t)=\left(t-\frac{9+\sqrt{17}}{16}\right)^2
   \left[12t^2+\frac{3\sqrt{17}-9}{2}t+\frac{9\sqrt{17}-15}{32}\right]\ge0$$

   completes the estimate. `polynomial_upper_bound` and `moment_upper_bound` supply these steps; `universal_upper_bound` applies them to every admissible rate vector.
3. **Realize sharpness with actual positive vectors.** Let $u=(9+\sqrt{17})/16$, so $0<u<1$. For every natural $m$, `sharpRates m` has $N=m+2$ coordinates,

   $$k_0=1/u,\qquad k_i=(m+1)/(1-u)\quad(i\ne0).$$

   `sharp_rates_positive` proves every coordinate positive. Their inverse rates sum to one, and for $j=2,3,4$ their power sums are

   $$R_j=u^j+\frac{(1-u)^j}{(m+1)^{j-1}}.$$

   With $z=1/(m+1)$, `sharp_value` evaluates the actual difference as

   $$-12[u^2+(1-u)^2z]^2+18[u^3+(1-u)^3z^2]
   -6\frac{u^4+(1-u)^4z^3}{u^2+(1-u)^2z}.$$

   Its denominator at zero is $u^2>0$. Continuity, $z\to0$, and the exact identity $f(u)=B$ give `sharp_limit`: these actual values tend to $B$.
4. **Pass to the full-set least upper bound.** Every term of this sequence lies in $V$. Any upper bound of all of $V$ therefore bounds the sequence and, by passage to its limit, is at least $B$. Together with the universal inequality this proves `IsLUB V upperBound`; `result` joins the two clauses.

### Relation of the sharpness family to the source

For $N=m+2$, dividing the constructed vector by its common tail rate gives the exceptional rate

$$
a=\frac{1-u}{u(N-1)}=\frac{A}{N-1},\qquad
A=\frac{1-u}{u}=\frac{5-\sqrt{17}}4.
$$

This finite parametrization differs from the source's $A/N$: their ratio is $N/(N-1)$ and tends to one. The proof evaluates its own finite vectors directly. The shared asymptotic scaling explains the source parameter; it neither identifies the two finite families nor proves a fixed-$N$ extremal-topology classification.

## Falsifier

A natural $N\ge2$ and a strictly positive real rate vector with $\mathcal S(k)-\mathcal K(k)>B$ would contradict the universal clause. An upper bound of every actual value in $V$ strictly smaller than $B$ would contradict the least-upper-bound clause. Testing only one topology or finitely many dimensions would not establish either full quantified clause.

A mismatch between the stated current-cumulant ratios and the reused inverse-rate definitions would instead invalidate the physical correspondence. The formal theorem proves the displayed rational expressions; it does not construct a stochastic process, prove the renewal identities, or identify an empirical current with those expressions. For $N=2$ the interpretation uses two successive oriented phase stages and one marked winding crossing. No physical $N=1$ realization is asserted.

## Evidence

Canonical source: `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.lean`, with public `result : claim`. The owning [Blueprint source](../Blueprint/D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.scribe.cs) attaches `OpenProblemResolutionClaim(Proved)` to this whole conjunction. It does not claim a resolution for a helper or only one clause.

The declaration statement identities are:

- `result`: `sha256:1fb913b270a37899363d7b9373b0cff4b7af3a6e69e54668ac61e9b88a9300da`;
- `claim`: `sha256:2dabc4b59745a968711c92cb4d2ee845e91fddc8b7559b80c1fd7e99246af4d4`.

The module Frozen statement identity is separately `sha256:39955e72b53c7d1b51847f2c3895548a03cc54355eac2eff023fd5a78039cf20`, at `Golden/Frozen/state/D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.lean.json`. This module identity is not the `result` declaration's statement identity.

The compiled result's axiom closure is `Classical.choice`, `Quot.sound` and `propext`, without `sorry` or a new axiom. Its whole-family audit source is `Reg/D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.lean`: the realization observes the difference on every natural size and real vector; its law preserves both the positivity-qualified universal bound and the full actual-set `IsLUB`. It supplies the source-equivalence bridge, a violating readout $B+1$, variation and sensitivity, and actual dependence witnessed by positive two-coordinate vectors. Its continuation is `.unknown`, not a theorem of inexhaustibility.

Primary v4 `main.tex` SHA-256: `0d8f9bf311a07990b64d4746e9ec4fb1e164deec23b270503642b94766baf84e`. Source locators, definitions and sign discrepancy are recorded in the existing literature note.

## Triage

`theorem`; resolution `proved` for the exact preregistered upper-endpoint conjunction. Admission uses the external open-problem-resolution basis in CLAUDE.md §3.2. The public result and retained theorem helpers have `proof_shape: bind-only`; each helper is consumed on the result's live proof path. Their algebra, moment reuse, explicit family evaluation and limit argument supply no separate escape witness. Proof shape and the external-resolution admission basis are distinct. Helpers and sharpness steps carry no additional external-problem credit.

### What the settlement shows

**Proved — `D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.result`.** Every finite positive real rate vector with $N\ge2$ satisfies $\mathcal S-\mathcal K\le B$, and $B$ is the least upper bound of exactly all its actual values over all such sizes and vectors. This includes arbitrary repeated rates and $N=2$. The proof uses the joint normalized moments and the two-case estimate, then actual positive-rate sharpness. It requires no extremal-topology assumption and no rational-rate restriction.

**Computed, not formalized.** None is used as settlement evidence.

**Open here.** The theorem does not establish strict finite unattainment, a finite-size optimizer or the full proposed extremal topology. It proves neither the lower endpoint of $\mathcal S-\mathcal K$ nor any new endpoint for the product, the sum, or another cumulant ratio. Those questions require their own statements and evidence; this resolution metadata does not cover them.

**Interpretive consequence and limits.** For positive unidirectional cycles to which the inverse-rate current formulas apply, the upper side of the detailed source difference interval has a universal proof independent of the numerically conjectured topology. Other results in the paper retain their own assumptions and evidence. In particular, an inference of multicyclicity from a violation still needs the relevant bounds for bidirectional cycles if that larger class is allowed. Finite-time currents, general bidirectional or multicyclic networks, standardized moments, and experimental realization remain outside this theorem.

## ASSUMED-UNVERIFIED

The accepted source screen's no-hit result remains bounded to its inspected literature and Lean-source scopes. The APS journal body, exact five-record OpenAlex membership and exhaustive theorem-equivalence search are unverified; no worldwide openness, global priority or original-proof claim follows.

The physical identification of the rational expressions with a stochastic current, the process construction, renewal asymptotics and empirical measurement are not formalized. The common-scale comparison with the source's $A/N$ parametrization explains the limiting relation and does not identify finite members. The strictness, topology and neighbouring questions listed in Triage are outside the proved claim. Canonical projection production, final independent review and publication are separate delivery obligations; this source dossier does not certify them.
