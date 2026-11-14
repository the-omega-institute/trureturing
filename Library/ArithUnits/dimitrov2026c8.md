---
bibkey: dimitrov2026c8
authors: S. I. Dimitrov
year: 2026
title: "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
doi: null
url: https://arxiv.org/abs/2606.12484v1
claim: "Conjecture 8 asserts the mixed-power Nesbitt lower bound for every integer n ≥ 2 and k ≥ 1, with pointwise function-value powers and unpowered inner sums."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovNesbittC8
license: source-reference
triage: anchor
---

# Dimitrov's mixed-power Nesbitt lower bound

The original locator is arXiv:2606.12484v1, §2, PDF page 5,
[Conjecture 8](https://arxiv.org/html/2606.12484v1#Thmconjecture8).
Its quantifier sentence is “For every integers $k\geq1$ and $n\geq2$, we have”.
With Euler's totient $\varphi$, Dedekind's
$\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$, and
$\sigma(n)=\sum_{d\mid n}d$, put

$$
A=\varphi(n)^k(\psi(n)+\sigma(n)),\quad
B=\psi(n)^k(\varphi(n)+\sigma(n)),\quad
C=\sigma(n)^k(\varphi(n)+\psi(n)).
$$

The conjecture is

$$
\frac A{B+C}+\frac B{A+C}+\frac C{A+B}\geq
\frac{n(n+1)^{k-1}(n-1)^k+(n-1)^{2k}+4n^2(n+1)^{2k-2}}
{2n^2(n+1)^{2k-2}+2n(n+1)^{k-1}(n-1)^k}.
$$

All powers are pointwise function-value powers. The sums inside $A,B,C$
are unpowered. The native Lean definitions are `Nat.totient`,
`OeisA344695GcdSigmaPsiPrimes.psi`, and `ArithmeticFunction.sigma 1`.
The natural exponent identity $2k-2=2(k-1)$ uses $k\ge1$, including $k=1$.

## Verified locator

https://arxiv.org/abs/2606.12484v1, §2, PDF page 5, Conjecture 8.

## Consumed Lean supplier

The analytic supplier is a modified Apache-2.0 source port from
[pro20541/dimitrov-conjectures-lean](https://github.com/pro20541/dimitrov-conjectures-lean/tree/95809b59deefd8dfad81e398250aedd7e1aea3b3),
commit `95809b59deefd8dfad81e398250aedd7e1aea3b3`.
The complete source
[FrontierMathLean/NesbittRatioInequality.lean](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean)
has SHA-256 `49f2083f76f2a7fb8283d205c8921023e8dbe493482764841ab697b5b64903ca`.
Its [formalization metadata](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/formalization.yaml)
names Michael Mazur as author and responsible maintainer; the
[README](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/README.md)
and [PROVENANCE](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/PROVENANCE.md)
disclose substantive OpenAI Codex generation under his direction.

The complete original Apache-2.0 license is distributed byte for byte at
[`docs/reports/licenses/dimitrov-LICENSE.txt`](../../docs/reports/licenses/dimitrov-LICENSE.txt),
11,357 bytes, SHA-256 `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
The pinned donor tree has no NOTICE file; the selected source has no separate
copyright header. The paper reference's `source-reference` field does not license
this Lean code.

Only this live cone is ported into `DimitrovNesbittC8`:

| Original declaration in `FrontierMathLean` | Local adaptation | Live consumer |
| --- | --- | --- |
| `balanced_pair_fraction_le` | Same telescope and proof; private visibility and receiver namespace. | `normalized_nesbitt_ratio_inequality` |
| `nesbitt_envelope_mono` | Same telescope and proof; private visibility and receiver namespace. | `normalized_nesbitt_ratio_inequality` |
| `normalized_nesbitt_ratio_inequality` | Same telescope and proof; private visibility and receiver namespace. | `result`, at $x=B/A$, $y=C/A$, $r=n(n+1)^{k-1}/(n-1)^k$ |

The normalized theorem requires exactly $1\le r$, $r\le x$ and $r\le y$.
The original `DimitrovLowerBoundsC4C5.mixed_bound` supplies these inequalities;
its `psi_ge` and `sigma_ge_psi` supply the arithmetic ordering. Their original
proofs are reused directly. The donor's equality theorem, strict envelope,
power theorem, paper conversion and arithmetic endpoints are not ported.
The port supplies no new mathematical content or escape witness.

The donor pins Lean `v4.32.0` and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`; the receiver pins Lean `v4.35.0`
and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The source-port form
preserves the receiver pins under A17.2.

## Receiver-pin retirement condition

Retire each local port exactly when an explicit candidate Mathlib declaration
at the receiver revision selected by `lake-manifest.json` compiles a direct
application over that interface's complete telescope, with no `sorry` and
axiom closure contained in `propext`, `Classical.choice`, `Quot.sound`.
The check covers the whole conclusion and all original hypotheses. Missing
suppliers or failed applications leave retirement false for that interface.
A successful replacement uses the native supplier directly and removes unused
local port proofs in the same change, preserving frozen identities through the
canonical writer. An unpinned upstream event is not the retirement criterion.
