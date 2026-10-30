---
slug: oeis-a115809-carryless-seventeen-nine-containment
bibkey: oeis2006a115809
doi: null
url: https://oeis.org/A115809
triage: theorem
motivation_gids:
  - D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment
---

# Containment of the A115809 carryless multiplier condition

## Problem

OEIS A115809 asks whether the integers satisfying its defining condition are
a subset of A115801. In the notation of the source, the exact question is

$$
\forall k\in\mathbb{N},\qquad
17k=C(49,k)\ \Longrightarrow\ 9k=C(25,k).
$$

Here $\mathbb{N}$ includes zero and the same $k$ occurs in both sides. The
products $17k$ and $9k$ are ordinary natural-number products. The operation
$C$ is binary coefficient convolution over $\mathrm{GF}(2)$:

$$
\operatorname{bit}(C(u,k),t)
=
\left(\sum_{i=0}^{t}
\operatorname{bit}(u,i)\operatorname{bit}(k,t-i)\right)\bmod 2.
$$

This is the carryless polynomial product described by OEIS A048720, not
ordinary multiplication. The source question and operation are recorded at
<https://oeis.org/A115809>.

## Motivation

The source asks for containment of two sets of nonnegative integers defined
by different ordinary and carryless multiplier pairs. A resolution must cover
every natural input, including zero, and preserve the distinction between
ordinary products and the coefficient-convolution operation.

## Gap

The A115809 record retains the question “Subset of A115801 ?”. The bounded
source and literature scope in
`Library/Digit/oeis2006a115809.md`, together with issue
<https://github.com/the-omega-institute/trureturing/issues/23260>, found no
exact answer in the checked sources or repository declarations. This records
the source-qualified open status; it does not assert exhaustive worldwide
openness or publication priority.

## Route

The proof uses the imported binary convolution definition and its equality
with the recursive binary product. A state is either rejecting or a pair
$(c,d)$ recording the ordinary multiplication carry and the remaining
exclusive-OR mask. Splitting the next input into its low binary digit gives a
transition for each of the two digits.

The finite relation of 101 paired states contains the initial pair, has the
required implication at input zero, and is closed under both transitions.
`Nat.evenOddRec` then transports the implication through the complete binary
expansion of every natural $k$. The initial pair yields exactly the displayed
implication, with no upper bound on $k$.

## Falsifier

A natural number $k$ satisfying $17k=C(49,k)$ but not
$9k=C(25,k)$ would refute the resolution. A mismatch between the stated
coefficient convolution and the imported operation, a failed terminal check,
or a transition leaving the 101-state relation would also invalidate the
route.

## Evidence

The truth anchor is
`D5/S1/Digit/Admissibility/CarrylessSeventeenNineContainment.result`.
Its compiled type is the exact all-natural implication above, and its proof
uses the 101-state relation and unbounded binary induction. The frozen
declaration uses only the allowed axiom closure `propext`,
`Classical.choice`, and `Quot.sound`.

The module keeps the checker terminal and result declarations and its
instance header. The typed Reg mirror preserves the source operation and
compiles, while its machine audit remains unresolved as
`IE-C050 ClosedTruthReadout`, reason `unclassified_form`, under the linked
exception
<https://github.com/the-omega-institute/trureturing/issues/23260#issuecomment-6477454945>.
That exception is disclosed evidence, not a validated registration and not a
substitute for the kernel or frozen state.

## Triage

`theorem`; resolution `proved` for the one source-authored containment
question stated above. The result preserves the 101-state mechanism, the
terminal and digit-closure checks, and induction over unbounded natural
inputs. It acknowledges the known carryless operation and answers the
A115809 question only in the displayed direction.

No uniform classification of multiplier pairs, converse implication,
additional resolution from A115801 or a neighboring sequence, worldwide
priority, or completeness claim is included.

## ASSUMED-UNVERIFIED

The literature and repository searches are bounded by the scope recorded in
the Library note and issue 23260. Exhaustive worldwide openness and priority
are unverified. The Reg audit readout remains unresolved under the linked
exception. The finite state relation is used only for this exact multiplier
pair and does not establish a general carryless classification.
