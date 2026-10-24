---
slug: grunwald-pales-2024-gini-stationary-test
bibkey: grunwaldpales2024gini
doi: null
url: https://arxiv.org/abs/2408.07658v1
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/GiniStationaryTest/Result.result
---

# Stationary characterization of Gini mean comparisons

## Problem

R. Grünwald and Zs. Páles, *Comparison of Gini means with fixed number of variables*, arXiv:2408.07658v1, §4, state:

> Conjecture 2. Assume that 0 = inf I · I⁻¹ and let n ≥ 3. Then ((r, s), (p, q)) ∈ Γ_n(I) if and only if, for all u₁, …, u_n ∈ ℝ₊ such that G^{[n]}_{r,s}(u₁, …, u_n) = 1, ∃ρ ∈ ℝ such that χ′_{p,q}(u_k) + ρχ′_{r,s}(u_k) = 0 (k ∈ {1, …, n}) the inequality 1 ≤ G^{[n]}_{p,q}(u₁, …, u_n) holds.

Here $I$ is a nonempty interval in $(0,\infty)$ and $\Gamma_n(I)$ consists of the parameter pairs satisfying $G_{r,s}(x)\le G_{p,q}(x)$ for every $x\in I^n$. The stationary test universally quantifies over positive normalized tuples satisfying the common-multiplier equations. It does not assert that every normalized tuple admits such a multiplier.

The formal reading is:

| Source object or condition | Lean encoding and meaning |
|---|---|
| $n\ge3$, $x\in I^n$ | `n : ℕ`, `3 ≤ n`, `x : Fin n → ℝ`, and `∀ i, x i ∈ I` |
| Nonempty positive interval $I$ | `I ⊆ Set.Ioi 0`, `I.OrdConnected`, and `I.Nonempty` |
| $\inf(I\cdot I^{-1})=0$ | `sInf ((fun z : ℝ × ℝ => z.1 / z.2) '' (I ×ˢ I)) = 0`; the set is precisely $\{a/b:a,b\in I\}$, rather than a product of two scalar infima |
| $G_{p,q}$, $p\ne q$ | `Defs.giniMean` delegates to `GiniMeanEndpointComparison.giniMean`, namely $(\sum x_i^p/\sum x_i^q)^{1/(p-q)}$ |
| $G_{p,p}$ | $\exp(\sum x_i^p\log x_i/\sum x_i^p)$, the equal-parameter branch of `Defs.giniMean` |
| $\chi_{p,q}$ | `Defs.chi`: $(t^p-t^q)/(p-q)$ for $p\ne q$, and $t^p\log t$ for $p=q$ |
| $\chi'_{p,q}$ | `Defs.chiDeriv p q t := deriv (Defs.chi p q) t` |
| $\Gamma_n(I)$ | `Defs.Gamma n I`: comparison for every tuple from $I$ |
| Stationary criterion | `Defs.stationaryTest n r s p q`: positivity, $G_{r,s}(u)=1$, and existence of a common real multiplier imply $1\le G_{p,q}(u)$ |
| Claimed equivalence | `Defs.claim`: all the displayed interval conditions, all $n\ge3$, and all real $r,s,p,q$ |

## Motivation

The proposed criterion would certify global comparison on intervals with arbitrarily large coordinate ratios using only interior stationary tuples after normalization. The positive half-line is such an interval, so a failure there refutes the full equivalence.

## Gap

The source proves the bounded-interval characterization in Theorem 7 and states Conjectures 1 and 2. Searches for the title, arXiv identifier 2408.07658, DOI 10.1007/s00025-025-02370-0, and the authors with “Conjecture 2”, “counterexample”, or “proof” found no settlement. Grünwald's 2025 Debrecen–Katowice seminar report (Ann. Math. Sil. 39(2) (2025), 381–394) restates the question. Conjecture 1 of the same paper is refuted in [the endpoint comparison dossier](grunwald-pales-2024-gini-mean-comparison.md). Citation indexes were not checked exhaustively. Interior stationarity alone does not control escape toward the boundary of the positive normalized simplex.

## Route

Fix any $n\ge3$, take $I=(0,\infty)$, and choose $(r,s)=(1,0)$ and $(p,q)=(2,-1)$. Normalization gives $\sum u_i=n$. The characteristic derivatives are

$$
\chi'_{1,0}(z)=1,\qquad \chi'_{2,-1}(z)=\frac{2z+z^{-2}}3.
$$

The multiplier equations therefore put every coordinate on one level of $g(z)=2z+z^{-2}$. Distinct positive points $\alpha,\beta$ on that level satisfy $\alpha+\beta=2(\alpha\beta)^2$, and the level contains at most two positive points. A nonconstant normalized tuple has values $\alpha<1<\beta$. Put $S=\alpha+\beta$ and $P=\alpha\beta$. Each coordinate satisfies $u_i^2=Su_i-P$ and $u_i^{-1}=(S-u_i)/P$, hence

$$
\frac1n\sum u_i^2=S-P,\qquad
\frac1n\sum u_i^{-1}=\frac{S-1}{P}.
$$

Since $(1-\alpha)(\beta-1)=(P-1)(2P+1)>0$, one has $P>1$. Thus

$$
\frac1n\sum (u_i^2-u_i^{-1})
=\frac{(P-1)(1-\alpha)(\beta-1)}P>0.
$$

Consequently $G_{2,-1}(u)>1$ on every nonconstant stationary tuple. The constant normalized tuple has every coordinate one and gives equality. This proves the stationary test.

## Falsifier

For $0<t<1$, use $x=(t,1,\ldots,1)$ and $k=n-1\ge2$. Then

$$
G_{1,0}(x)=\frac{t+k}{k+1},\qquad
G_{2,-1}(x)^3=\frac{t(t^2+k)}{1+kt}.
$$

The identity

$$
(t+k)^3(1+kt)-(k+1)^3t(t^2+k)
=k(t-1)^3(t-k^2)>0
$$

gives $G_{1,0}(x)>G_{2,-1}(x)$ because all denominators are positive and cubing preserves order. In particular, $n=3$ and $t=1/2$ give $G_{1,0}(x)=5/6$ and $G_{2,-1}(x)^3=9/16<125/216=(5/6)^3$. The pair passes the stationary test but lies outside $\Gamma_n((0,\infty))$ for every $n\ge3$.

## Evidence

The theorem `D5/S3/ArithSums/GiniStationaryTest/Result.result` has the unconditional type `¬ Defs.claim`. Its axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Its mathematical dependencies are `Result.counterexample_family`, `Stationary.stationaryTest_one_zero_two_negOne`, `Stationary.chiDeriv_parameters`, `Witness.not_mem_Gamma`, `Witness.witness_comparison`, and `Witness.witness_identity`, together with the private stationary level, moment, and finite-sum helpers. The existing unequal-parameter mean and `highTuple` come from `GiniMeanEndpointComparison`; real-power, derivative, finite-sum, and conditional-infimum facts come from Mathlib. The family theorem supplies both the stationary criterion and nonmembership for the same $n$ and parameters, and `result` specializes both conjuncts at $n=3$. The quotient set of $(0,\infty)$ equals $(0,\infty)$, whose infimum is zero.

ChatGPT Pro supplied the counterexample route; the Lean evidence supports the first triage item.

## Triage

1. **PROVED — the stationary characterization fails in every dimension $n\ge3$.** `Result.counterexample_family` proves that $(1,0),(2,-1)$ passes the stationary test and is outside $\Gamma_n((0,\infty))$. `Stationary.stationaryTest_one_zero_two_negOne` proves the stationary part for every nonzero dimension. `Result.result` refutes the full universally quantified claim.

2. **PROVED in prose — every positive parameter scale.** Fix $a>0$ and set $v_i=u_i^a$. For either parameter pair $(r,s)=(1,0)$ or $(2,-1)$,
   $G_{ar,as}(u)=G_{r,s}(v)^{1/a}$ and $\chi'_{ar,as}(u_i)=u_i^{a-1}\chi'_{r,s}(v_i)$. The positive factor $u_i^{a-1}$ cancels from each multiplier equation, so normalization and stationarity transfer to $v$. The proved stationary criterion and the increasing map $z\mapsto z^{1/a}$ give the scaled stationary criterion. Conversely, take $x=(t^{1/a},1,\ldots,1)$ for $0<t<1$; the same identity transfers the strict comparison reversal to $(a,0),(2a,-a)$.

3. **PROVED in prose — boundary escape.** For $0<\varepsilon<1$, the positive tuple $u=(\varepsilon,b,\ldots,b)$ with $b=(n-\varepsilon)/(n-1)$ has mean one. Its objective is
   $\sum(u_i^2-u_i^{-1})=\varepsilon^2+(n-\varepsilon)^2/(n-1)-1/\varepsilon-(n-1)^2/(n-\varepsilon)$, which tends to $-\infty$ as $\varepsilon\downarrow0$. Thus the objective has infimum $-\infty$ on the positive normalized simplex, despite being nonnegative at all its stationary tuples.

4. **PROVED in prose — comparison implies the stationary criterion.** For any admissible $I$ and positive tuple $u$, put $m=\min u_i>0$ and $M=\max u_i$. The zero quotient infimum provides $a,b\in I$ with $a/b<m/M$. Set $c=a/m>0$. Every $cu_i$ lies between $a$ and $b$, hence belongs to $I$ by interval connectedness. Comparison on $I$ and homogeneity $G_{r,s}(cu)=cG_{r,s}(u)$ give comparison at $u$ for all parameters, including equal parameters. If $G_{r,s}(u)=1$, the required inequality follows, whether or not $u$ is stationary.

5. **COMPUTED — a rational three-variable instance.** At $(1/2,1,1)$, the cubed comparison is $9/16<125/216$, equivalently $1944<2000$. These exact arithmetic values illustrate the proved family.

6. **OPEN — the comparison region.** What is a correct characterization of $\Gamma_n(I)$ when $\inf(I\cdot I^{-1})=0$?

## ASSUMED-UNVERIFIED

The journal version's text is unverified; the quotation and locators refer to arXiv:2408.07658v1. The literature scope does not establish an exhaustive literature or priority claim.

The positive-scale extension, boundary-escape limit, and general surviving implication are proved in prose above, not in the companion Lean modules. The Lean family fixes parameter scale $a=1$ and covers every $n\ge3$.
