---
slug: khani-valizadeh-zarei-2026-iterated-beatty-extension
bibkey: khani2026iteratedbeatty
doi: null
url: https://arxiv.org/abs/2607.12817v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.result
---

# A negative answer to the universal iterated Beatty extension

## Problem

Mohsen Khani, Ali N. Valizadeh and Afshin Zarei, *A Note on Iterated
Beatty Sequences*, arXiv:2607.12817v1, Question 1 on printed page 8, ask:

> A natural question is whether our theorem holds also for irrationals
> belonging to the following set:
> (1, 2.618∼) = (1, 2.118∼) ∪ (2.118∼, 2.618∼).

The displayed typography is normalized. The page-one theorem has exact
threshold $c=(3+\sqrt5)/2$. The internal split $\rho$ is the greatest real
root of $P(t)=t^4-2t^3-t+1$. This dossier anchors only Question 1, with the
entire interval $(1,c)$, including $\rho$ despite its omission from the
printed union. Question 2 is outside the statement.

For real $\alpha>1$, write $f_\alpha(k)=\lfloor\alpha k\rfloor$ and
$\{t\}=t-\lfloor t\rfloor$. On the explicitly registered positive-natural
interpretation, the complete proposed extension is: for every irrational
real $1<\alpha<c$, every natural $n\ge1$ and every natural $x\ge1$,

$$
\bigl(\exists k\in\mathbb N,\ k\ge1\ \land\ f_\alpha^{[n]}(k)=x\bigr)
\quad\Longleftrightarrow\quad
\left\{
\begin{aligned}
&1-\frac1\alpha<\left\{\frac x\alpha\right\}<1,\\
&\forall i\in\mathbb N,\ 2\le i\le n:\quad
1-\frac2\alpha<\left\{\frac x{\alpha^i}\right\}
-\frac{\{x/\alpha^{i-1}\}}\alpha<1-\frac1\alpha.
\end{aligned}
\right.
$$

Here $f_\alpha^{[n]}$ is actual repeated composition, with every intermediate
floor; it is not $k\mapsto\lfloor\alpha^n k\rfloor$. All fractional tests,
strict inequalities and index endpoints are retained. The source's
positive-versus-zero convention remains unverified; it is not silently
identified with the registered interpretation.

## Motivation

The range characterization relates a discrete dynamical orbit to real
fractional-part tests. The question asks whether that equivalence survives
below its published threshold. The mathematical claim and its literal
negation are `claim` and `result` in
`D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.lean`.
The source and preregistered full event are associated with
[issue #29668](https://github.com/the-omega-institute/trureturing/issues/29668).

## Gap

Membership in a floor-map iterate does not force the proposed upper bound
at every fractional index. A positive fixed point supplies an actual range
member at the third iterate while its index-three test fails. This
counterexample negates the universal event; it does not characterize all
moduli for which the equivalence holds, and it does not refute the original
theorem for $\alpha>c$.

## Route

Take $\alpha=\sqrt2$, $n=3$, $x=2$ and preimage $k=2$.
The modulus is irrational and $1<\sqrt2<3/2<c$.
Because $2<2\sqrt2<3$, one has $f_{\sqrt2}(2)=2$ and hence
$f_{\sqrt2}^{[3]}(2)=2$. On the other hand,

$$
\left\{\frac2{(\sqrt2)^2}\right\}=0,
\qquad
\left\{\frac2{(\sqrt2)^3}\right\}=\frac1{\sqrt2}.
$$

The index-three expression equals $1/\sqrt2$, whereas the proposed strict
upper bound is $1-1/\sqrt2$. Since $2/\sqrt2=\sqrt2>1$, the required
inequality fails. These statements use the same modulus and the same actual
iterate-range member.

The real/Nat bridge preserves the source map: for $\alpha>1$ and natural
$k$, the real product $\alpha k$ is nonnegative, so natural floor and integer
floor give the same integer value. For positive $k$, $k\le\alpha k$
implies $k\le\lfloor\alpha k\rfloor$. Induction keeps all intermediate
iterates positive. The formal `nativeBeatty` uses natural floor of real
multiplication, and `nativeRange` uses `Function.iterate` with a positive
natural preimage. The input and preimage of the counterexample are both
$2$, so adding zero to either domain preserves this same counterexample.

The placement in the lower printed branch also follows on paper:
$P(2)=-1$ and $P(3)=25$. The intermediate value theorem gives a root in
$(2,3)$, so the greatest root satisfies $\rho>2>3/2>\sqrt2$.
This expository polynomial argument is not a separate kernel theorem in
the delivered module.

## Falsifier

The witness mechanism would fail if the native floor map did not fix $2$
at modulus $\sqrt2$, if third-iterate membership failed, or if the
index-three upper bound actually held. The literal Lean theorem negates
the full `claim`; no fractional-test failure is assumed as a premise.
A positive theorem on a restricted family or a single-step power-floor
surrogate would not settle this event.

## Evidence

The mathematical source has four necessary definitions (`nativeBeatty`,
`nativeRange`, `fractionalTest`, `claim`) and one public theorem (`result`).
Its exposition is
`Blueprint/D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.scribe.cs`.
The typed `Refuted` claim is attached only to `result`.

The source is arXiv:2607.12817v1, with main characterization on printed
page 1 and Question 1 on printed page 8. The inspected PDF SHA-256 is
`5907ce19916db99b8e34fbecee5ce6bf9d693f2a769d2267bfb9952c2d5f037f`.
The [Library note](../Library/Certificates/khani2026iteratedbeatty.md) records the
bounded literature screen. The read Chew–Tanny 1999 author DVI concerns
restricted quadratic-modulus and commutator results. The publisher text
for DOI `10.1080/10236190108808279` returned 403 and was not read; its
identity with the author manuscript is unverified. Inspected Dekking
results concern restricted quadratic double iterates. No exact supplier
was found in the inspected D5/private, pinned Mathlib or third-party
scopes. Missing readings are retained below; this is not a global absence
or priority assertion.

## Triage

`theorem`: the literal universal extension has a negative answer.
The evidence has the following distinct scopes.

| Conclusion | Evidence and boundary |
| --- | --- |
| Negation of the full registered `claim` | Kernel-checked `result : Not claim`, with actual natural floor composition and all quantified strict tests retained. |
| Fixed-point mechanism and the failed third test | The proof of `result`; the calculation above also gives a prose proof. No separate helper theorem is claimed. |
| Same counterexample under zero-inclusive naturals | Prose proof: the same positive input and positive preimage remain admitted. The source convention itself is unresolved. |
| Counterexample lies in the lower printed branch | Prose proof via $P(2)=-1$, $P(3)=25$ and the intermediate value theorem; not a separate kernel result. |
| Original theorem for irrational $\alpha>c$ | Literature-attested scope of the source theorem; unchanged by this refutation. Its proof is not reverified here. |
| Repaired fractional criteria, uniform mixed-modulus results or a sharp validity threshold | Open in the retained evidence; no such theorem is supplied. |
| Question 2 | Outside this dossier and not solved here. |

The counterexample does not assert failure at every modulus, a smallest
counterexample, worldwide priority or a new narrowed substitute problem.

## ASSUMED-UNVERIFIED

The source's convention on naturals including zero is unverified. The
positive witness makes that ambiguity immaterial to this negative answer.
The Chew–Tanny publisher text and manuscript identity remain unverified;
MathDB challenge pages and OpenAlex rate-limited readings remain missing.
The bounded search does not establish global openness or absence of prior
solutions.
