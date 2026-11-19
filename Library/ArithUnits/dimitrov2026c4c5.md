---
bibkey: dimitrov2026c4c5
authors: S. I. Dimitrov
year: 2026
title: "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III"
doi: null
url: https://arxiv.org/abs/2606.12484v1
claim: "Conjectures 4 and 5 assert the displayed reciprocal-product lower bounds for every integer n ≥ 2 and k ≥ 1, with φ Euler's totient, ψ Dedekind's function, and σ the positive-divisor sum."
strata_touched:
  - D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5
license: source-reference
triage: anchor
---

# Dimitrov's reciprocal-product lower bounds

S. I. Dimitrov's arXiv:2606.12484v1, §2 (PDF p.4), states two conjectures for every integer
$n\ge2$ and $k\ge1$. The functions are Euler's totient $\varphi(n)$, Dedekind's
$\psi(n)=\prod_{p^e\parallel n}p^{e-1}(p+1)$, and the positive-divisor sum
$\sigma(n)=\sum_{d\mid n}d$. Powers in both source expressions are pointwise powers of
function values.

Conjecture 4 is the reciprocal product of
$\varphi(n)^k(\psi(n)+\sigma(n))$,
$\psi(n)^k(\varphi(n)+\sigma(n))$, and
$\sigma(n)^k(\varphi(n)+\psi(n))$, bounded below by
\[
\frac{5n(n+1)^{k-1}(n-1)^k+2(n-1)^{2k}+2n^2(n+1)^{2k-2}}
{n(n+1)^{k-1}(n-1)^k}.
\]
Conjecture 5 replaces each mixed sum by the sum of the corresponding pointwise powers
and has right side
\[
\frac{10(n-1)^{2k}+7(n^2-1)^k+(n+1)^{2k}}
{(n-1)^{2k}+(n^2-1)^k}.
\]

The D5 module proves both complete statements. Its native bridge establishes
$0<\varphi(n)\le n-1<n+1\le\psi(n)\le\sigma(n)$; the remaining argument is an ordered
reciprocal-product inequality applied first to the mixed terms and then to their
pointwise-power specialization. The denominator facts use $n\ge2$ and $k\ge1$ directly.

## Verified locator

https://arxiv.org/abs/2606.12484v1, §2, PDF page 4, Conjectures 4 and 5.

## Lean analytic supplier

The paper citation's `source-reference` license records a reference to Dimitrov's
paper; it does not license the Lean code. The analytic supplier is a **modified
Apache-2.0 source port** from
[pro20541/dimitrov-conjectures-lean](https://github.com/pro20541/dimitrov-conjectures-lean/tree/95809b59deefd8dfad81e398250aedd7e1aea3b3),
fixed at commit `95809b59deefd8dfad81e398250aedd7e1aea3b3`.
Its [formalization metadata](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/formalization.yaml)
names Michael Mazur as author and responsible maintainer. Its
[README](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/README.md)
and [provenance](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/PROVENANCE.md)
disclose substantive OpenAI Codex generation under his direction. The donor's
full-range arithmetic endpoints concern Conjectures 1 and 3, not the Conjecture 4
and 5 endpoints here. Reuse of its analytic suppliers implies no priority claim
for these endpoints and supplies no new mathematical content or escape witness.

The complete original
[LICENSE](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/LICENSE)
is distributed byte for byte at
[`docs/reports/licenses/dimitrov-LICENSE.txt`](../../docs/reports/licenses/dimitrov-LICENSE.txt).
It contains 11,357 bytes with SHA-256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
The complete pinned donor tree contains no NOTICE file; the selected Lean files
contain no separate copyright header. Their relevant explanatory comments and
the upstream attribution are retained. The license appendix's example copyright
line is license template text, not an attribution to an invented copyright holder.

The source files, hashed over their complete original bytes, are:

| Immutable original source | SHA-256 |
| --- | --- |
| [FrontierMathLean/AbstractInequality.lean](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/AbstractInequality.lean) | `a7ccecff1f70b9e3f7e386938ece5078c8590dcd210dde9296759a750d61521e` |
| [FrontierMathLean/ThreeTermInequality.lean](https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/ThreeTermInequality.lean) | `4835ffbffca0e7ced2ef01041cb82b4613e239432c5071c8947118c773ef2f76` |

Only the following consumed cone is ported, inside the existing
`D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5.lean` module:

| Original declaration in `FrontierMathLean` | Local interface and adaptation | Consumer |
| --- | --- | --- |
| `add_inv_mono_on_one` (`AbstractInequality.lean`) | Private `h_mono`; `r := u`, `x := v`, `hr := hu`, `hrx := huv`; `one_div` converts the existing `1 / u` and `1 / v` interface to inverse notation. The positivity, inverse bound, product and `field_simp`/`nlinarith` proof are retained. | Local `normalized_three_variable_inequality`, twice. |
| `normalized_three_variable_inequality` (`AbstractInequality.lean`) | Local `have` with the complete original `{x y r : ℝ}` telescope and hypotheses `1 ≤ r`, `r ≤ x`, `r ≤ y`; its two monotonicity calls use `h_mono` with `one_div` normalization. Positivity, squared difference and `linarith` are retained. | Local `three_term_ratio_inequality`, at `x := B / A`, `y := C / A`. |
| `three_term_ratio_inequality` (`ThreeTermInequality.lean`) | Local `have` with the complete original `{A B C r : ℝ}` telescope, three positivity hypotheses and `1 ≤ r`, `r ≤ B / A`, `r ≤ C / A`; the normalized application and `field_simp`/`ring` conversion are retained. | Existing private `ordered_reciprocal_bound`, at `A := X`, `B := Y`, `C := Z`, `r := R`. |

The final ordered application derives positivity of `Y` and `Z` from the existing
ordering, and `R ≤ Z / X` by transitivity and Mathlib's
`div_le_div_of_nonneg_right hYZ hX.le`. This is the direct native supplier for
division monotonicity; `one_div` restores the existing reciprocal interface.
The port changes local names/visibility, proof packaging and reciprocal notation
only. It adds no top-level declaration. The donor's power inequality, paper-bound
conversion, challenge placeholders and arithmetic/equality development are not
ported. The existing arithmetic bridge and both complete C4/C5 proofs remain
separate from the port.

The donor pins Lean `v4.32.0` and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`; this receiver pins Lean `v4.35.0`
and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. These incompatible
pins select the source-port form rather than a Lake dependency under A17.2.

## Receiver-pin retirement condition

For each of the three interfaces above, retirement is true exactly when explicit
candidate Mathlib declarations/modules at the receiver revision actually
selected by `lake-manifest.json` compile exact applications over the complete
ported telescope, with no `sorry` and axiom closure contained in `propext`,
`Classical.choice`, and `Quot.sound`. The finite replacement check must cover the
whole conclusion and all original hypotheses; a missing supplier or a failed
check makes retirement false for that interface. This does not depend on an
unpinned upstream acceptance event.

A successful replacement check requires replacing the corresponding port proof
by direct Mathlib references and removing unused local port `have`s in the same
change. Preserve existing frozen names/statements through direct applications or
a separately justified canonical migration; do not delete frozen members to
retire a port. No donor declaration is counted as new mathematical content.
