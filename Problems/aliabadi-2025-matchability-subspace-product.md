---
slug: aliabadi-2025-matchability-subspace-product
bibkey: aliabadi2025matchabilityii
doi: 10.7151/dmgaa.1461
url: https://www.dmgaa.uz.zgora.pl/publish/pdf.php?doi=1461
triage: theorem
motivation_gids:
  - D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.result
---

# Aliabadi's uncapped subspace-product conjecture is false

## Problem

Mohsen Aliabadi, *Conditions for matchability in groups and field extensions II*,
Discussiones Mathematicae General Algebra and Applications 45 (2025), 135–157,
section 5.1, Conjecture 38, printed page 154 / PDF page 20, states:

> Let $K\subset L$ be a field extension and $A,B\subset L$ be a $K$-subspace
> of $L$ of finite positive dimensions. Assume further that for every
> $a,b\in L$ and every nontrivial proper finite intermediate subfield
> $K\subset M\subsetneq L$, we have
>
> $$\dim_K(aM\cap A)+\dim_K(bM\cap B)\le [M:K]+1.$$
>
> Then for all $K$-subspaces $S\subset A$ and $T\subset B$, the following holds
>
> $$\dim_K\langle ST\rangle\ge\dim_K S+\dim_K T-1.$$

The same statement is Conjecture 5.1 in arXiv:2309.14664v1, PDF page 14,
and v2/v3, PDF page 15. Section 2.2 defines the brackets as the $K$-linear
span of the actual product set in $L$. The
[source note](../Library/Factorization/aliabadi2025matchabilityii.md)
records the primary versions, DOI and locators. The sole target is the
whole original universal assertion. Preregistration:
[#23409](https://github.com/the-omega-institute/trureturing/issues/23409).

### Statement correspondence

| Source clause | Formal counterpart and witness |
| --- | --- |
| Arbitrary field extension $K\subset L$ | `claim` quantifies fields with a `K`-algebra structure on `L`. The witness is the actual field `AdjoinRoot (X^7-C 2)` over $\mathbb Q$, with the canonical injective algebra map and degree seven. |
| Finite positive-dimensional $A,B$ | Both finite-dimensional hypotheses and both positive-finrank hypotheses occur in `claim`; $A=B=\operatorname{powerSpan}(6)$ has dimension six. |
| Every $a,b\in L$, including zero | Both unrestricted scalar binders occur in `intersectionPremise`; `translate` maps the underlying submodule of $M$ by actual multiplication by the scalar. |
| Every finite nontrivial proper intermediate field | `IntermediateField K L`, `⊥ < M`, `M < ⊤`, and `FiniteDimensional K M`. Neither endpoint is included. Prime degree proves that no witness field has such an $M$. |
| Both intersection dimensions and $[M:K]+1$ | Submodule infima and finranks in `intersectionPremise` express the exact displayed inequality. No assumed certificate replaces it. |
| Every allowed $S\subset A$, $T\subset B$ | `claim` quantifies all submodules with `S ≤ A` and `T ≤ B`, including the zero subspaces. The counterexample has both containments strict, so it also refutes the strict reading of the printed subset symbols. |
| Actual $\langle ST\rangle$ | `Submodule.span K ((S : Set L) * (T : Set L))`, using field pointwise multiplication. |
| Uncapped lower bound | `finrank K S + finrank K T - 1 ≤ finrank K (span ...)`; natural subtraction gives the same inequality truth value as integer subtraction, including zero dimensions. |
| Whole-claim negation | The sole public theorem `result : ¬ claim` has no extra mathematical premise. |

The matching definitions in the introduction use equal dimensions and
$1\notin B$ when defining matchability. Conjecture 38 states neither
matchability nor these conditions as an added premise. The witness
nonetheless has $A=B$ and $S=T$, with $1$ absent from all four spaces.
It also has $S<A<L$ and $T<B<L$. No assumption that a subspace contain
$1$, that the ambient extension be infinite, or that the dimension sum
be small is inserted. No ambient cap replaces the source conclusion.

## Motivation

Section 5.1 seeks a linear counterpart of the group product-set estimate
used for sufficient matchability conditions. The conjecture would force
expansion of every pair of contained subspaces from bounds on translated
intermediate-field intersections. Its universal conclusion must also
respect finite ambient dimension. A field of prime degree separates that
obstruction from all the proper intermediate-field tests in the premise.

## Gap

The premise omits the ambient intermediate field $M=L$. In prime degree
there is also no nontrivial proper intermediate field. Thus the premise
places no restriction on $A$ and $B$ in this case, while the proposed
conclusion can demand dimension larger than $[L:K]$. The obstruction
persists for strict subspaces and for spaces avoiding $1$; it is not
caused by choosing an endpoint or a zero-dimensional space.

## Route

Set $K=\mathbb Q$, $f=X^7-2$, $L=\mathbb Q[X]/(f)$ and let $\alpha$ be the
class of $X$. Eisenstein at the prime ideal $(2)$ first proves the integer
polynomial irreducible; its monicity gives primitiveness, and Gauss's
lemma transfers irreducibility to $\mathbb Q[X]$. `AdjoinRoot` then supplies
the field and its canonical algebra structure. Its power basis gives

$$[L:\mathbb Q]=7,\qquad \alpha^7=2,\qquad
1,\alpha,\alpha^2,\ldots,\alpha^6\text{ a basis}.$$

Define

$$A=B=\operatorname{span}_{\mathbb Q}\{\alpha,\ldots,\alpha^6\},\qquad
S=T=\operatorname{span}_{\mathbb Q}\{\alpha,\ldots,\alpha^5\}.$$

The selected powers are distinct basis entries. Their spans have
dimensions six and five; the omitted constant entry proves $1$ is absent.
The inclusion of the five powers among the six, together with their
strict dimension inequality, proves $S<A$ and $T<B$. Dimension six is
less than seven, so $A$ and $B$ are proper ambient subspaces.

`IntermediateField.isSimpleOrder_of_finrank_prime` proves that every
intermediate field is bottom or top. This discharges the full universal
premise for every scalar pair and every finite nontrivial proper $M$.
For the identical actual product span appearing in `claim`, the ambient
finrank bound gives

$$\dim_{\mathbb Q}\langle ST\rangle\le7<9=5+5-1.$$

Applying the universal assertion to these fields and subspaces yields
a contradiction. Exact equality $\langle ST\rangle=L$ is unnecessary and
is not asserted as proved. The endpoint negates the whole original claim,
not only a proposition about the selected parameter values.

## Falsifier

An omitted source condition excluding this finite extension or these
subspaces, a different meaning of the printed intermediate-field range,
or a failure of irreducibility, the actual quotient field, the power-basis
dimensions, or the actual product-span bridge would invalidate the route.
All four primary versions have the same quantified uncapped conclusion;
the source conditions above are matched by the formal claim and witness.
The optional exact product-span equality is outside the required argument.

## Evidence

The formal endpoint is
`D5/S3/Factorization/Galois/AliabadiSubspaceProductRefutation.result`, with
literal type `Not claim`; `claim` has literal type `Prop`. The Scribe
binds the dossier to this one endpoint with a Refuted
`OpenProblemResolutionClaim`. The public definitions describe the field,
translated-intersection premise, universal claim, power spans and realized
certificate. The private `countermodel_verified` proves that certificate;
`result` uses its premise, dimensions, containments and product upper bound.

The exact reused suppliers in pinned Mathlib include the Eisenstein and
Gauss irreducibility theorems, `AdjoinRoot.powerBasis'`, the prime-degree
intermediate-field theorem, `finrank_span_eq_card`, and
`Submodule.finrank_le`. No external Lean dependency is selected.
The axiom closure is contained in `Classical.choice`, `Quot.sound` and
`propext`; there is no `sorry` or new axiom. The source-authored inventory
has six public definitions, two public abbreviations, nine private
implementation theorems, two private definitions, two private instances,
and one public theorem. Compiler-generated companions are not additional
authored public results.

The proof organization is `bind-only`. Its admission basis is the
external named `open-problem-resolution` under #23409, and its utility is
`certified-instance` with `refutes` pointing to the literal whole `claim`.
The designated result is exempt from four-slot escape registration;
there is no other authored public theorem requiring a Reg mirror.
No new general method or escape witness is claimed.

## Triage

Tier 1: a short refutation of the complete original published conjecture.
The 2023 preprint and 2025 journal statement provide the named target;
the bounded source/literature screen in #23409 found no prior settlement
in its searched scope. This is not an exhaustive literature or priority
certificate. Aliabadi–Zerbib's matroid Question 2.7 is a different problem.

### What the settlement shows

| Conclusion or boundary | Evidence status |
| --- | --- |
| Whole uncapped Conjecture 5.1 / Conjecture 38 | Proved in Lean: `result : ¬ claim`. |
| Actual field, degree seven, root relation, dimensions, strictness and absence of $1$ | Proved in Lean: the private field/basis lemmas and `countermodel_verified`. |
| Complete translated-intersection premise | Proved in Lean from prime-degree intermediate-field simplicity. |
| Product-span dimension at most seven | Proved in Lean for the actual pointwise product span. |
| Product-span dimension exactly seven | Not proved or required here. |
| A repaired bound with an ambient cap, a dimension-sum restriction, or an infinite ambient extension | Unresolved by this result; each is a different assertion requiring its own hypotheses and proof. |
| Conjecture 5.2 / journal Conjecture 39 on Chowla subspaces | Unresolved by this result. |

The failure mechanism is finite ambient saturation combined with omission
of $L$ from the field tests. Any linear matchability argument relying on
the universal estimate must replace or restrict that estimate. The source
presents the estimate as a proposed future extension of a group result;
the refutation does not negate that group theorem, the separate Chowla
conjecture, or the paper's independently proved matching theorems.
The surviving certified facts are the explicit field and subspaces and
their full premise together with the incompatible lower and upper bounds.
No repair or uniform family theorem is inferred from this one certificate.

## ASSUMED-UNVERIFIED

Completeness of the bounded external literature and Lean-ecosystem searches,
worldwide priority, and absence of uninspected settlements remain
ASSUMED-UNVERIFIED. The historical supplier-search ordering is recorded in
the completed source handoff, rather than independently timestamp-certified
by the mathematical proof. It includes repository declarations, including
private originals, then pinned Mathlib, then a bounded external screen;
exact generic suppliers are directly reused. The formal result makes no
claim about exhaustive theorem discovery or method novelty. The stronger
exact product-span equality and the alternative repaired conjectures
listed above are not proved by this endpoint.
