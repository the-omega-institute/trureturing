---
slug: hardin-barker-a202330
bibkey: hardinbarker2018a202330
doi: null
url: https://oeis.org/A202330
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.result
---

# The complete four-column A202330 event

## Problem

For each integer index $n\ge1$, let $a_n$ count all labeled arrays
$A:\operatorname{Fin}(n+1)\times\operatorname{Fin}(4)\to\{0,1\}$.
Every row and every column must have nondecreasing consecutive windows of two
bits interpreted as ordinary binary integers. Thus each consecutive triple
$(u,v,w)$ obeys $2u+v\le2v+w$. There is no periodic boundary or quotient.

The single event is the conjunction

$$12a_n=n^4+16n^3+83n^2+176n+156\quad(n\ge1),$$

$$\sum_{n\ge1}a_nX^n=
\frac{X(36-98X+112X^2-61X^3+13X^4)}{(1-X)^5}
\quad\text{in }\mathbb Q[[X]],$$

$$a_n=5a_{n-1}-10a_{n-2}+10a_{n-3}-5a_{n-4}+a_{n-5}
\quad(n\ge6).$$

## Motivation

R. H. Hardin's OEIS A202330, revision 8, gives the native array count and the
empirical quartic. Colin Barker's FORMULA block gives the conjectural generating
function and recurrence. The immutable source, exact quotation, attribution and
CC BY-SA 4.0 license are in `Library/Certificates/hardinbarker2018a202330.md`.
[Issue #28964](https://github.com/the-omega-institute/trureturing/issues/28964)
preregisters all three clauses as one event. The source offset is `1,1`.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| All labeled `(n+1)` by four binary arrays | `count n`, the cardinality of the subtype of `Fin (n+1) x Fin 4 -> Bool` satisfying `valid` |
| Ordinary two-bit integer windows in every row | `horizontal` uses `bit : Bool -> Int` before arithmetic, with both starting positions in `Fin 2` |
| Every column and every in-bounds consecutive row triple | The second conjunct of `valid`, with `i+2<n+1` and every `j : Fin 4` |
| Quartic for every positive index | First conjunct of `claim` |
| Rational formal series with zero constant coefficient | `generatingSeries` and the second conjunct of `claim` |
| Signed recurrence for all indices at least six | Third conjunct of `claim`, in `Int` |
| One complete event | The single public theorem `result : claim` |

## Gap

The missing mathematical link in programs that evaluate the formulas is the
native-array cardinality.

## Route

`rowEquiv` and `arrayEquiv` preserve all coordinates
and identify the native subtype with good ordered row words. The public
`TransferMatrix.cardMatrix` applies with all 36 ordered pairs, exact singleton
initial fibres and exact zero-or-one transition fibres.

Write $F=m^4+12m^3+41m^2+54m+48$,
$G=2(m+1)(m+2)(m+6)$, $H=6(m+1)(m+4)$ and $L=12(m+2)$.
In the row order `0000,0001,0010,0011,0111,1111`, the scaled continuation vector
is the flattened array

$$V(m)=\begin{pmatrix}
F&G&G&H&L&12\\
0&G&0&H&L&12\\
0&0&G&H&L&12\\
0&0&0&H&L&12\\
0&0&0&0&L&12\\
0&0&0&0&0&12
\end{pmatrix}.$$

The finite initial identity is $12T^2\mathbf1=V(2)$ and the polynomial
transition identity is $TV(m)=V(m+1)$. Induction proves the identity for all
natural exponents $m\ge2$. Summing its coordinates, with source index
$n=m+1$, gives the quartic. The counts at one and two supply the two boundary
indices. The fifth difference gives the recurrence. Multiplication of the
zero-constant series by $(1-X)^5$ gives coefficients
`0,36,-98,112,-61,13` and zero thereafter; its constant coefficient is one,
so inversion gives the stated formal generating function.

## Falsifier

A source-valid array at a positive index whose total native count violates the
quartic, or a positive-index coefficient violating the formal series or signed
recurrence, refutes the conjunction. The mathematical domain includes the
incomparable rows `0001` and `0010`. Neither a finite sample of heights nor a
sequence defined from the quartic replaces this domain.

## Evidence

The designated formal source is
`D5/S3/Combinatorics/TraceAvoidingArrays/HardinA202330.lean` and its matching
Blueprint Scribe. The proof uses only the existing transfer theorem, finite
cardinality transport, polynomial identities, induction and formal power-series
algebra. Canonical compilation and scoped reporting succeed for the D5 source
and its Reg mirror at these mathematical sources. Verification of the emitted
Blueprint formulas and the remaining delivery checks are unfinished. No freeze
or solved-event count is asserted by this dossier.

## Triage

The source unit contains the complete native target and a direct Lean proof.
Its selected Scribe script and candidate whole-sequence audit compile. The
source-owner audit remains unresolved because source selection and a validation
certificate are absent. It remains unfinished under
[issue #29528](https://github.com/the-omega-institute/trureturing/issues/29528)
and the CLAUDE §3.9 linked-issue exception. Rendering, freeze, required CI,
integration and delivery remain unfinished; no solved-event credit is asserted.

## ASSUMED-UNVERIFIED

The bounded literature search found no covering native-array theorem in the
searched sources. Worldwide absence of a prior proof and unpublished ownership
are unverified. Other widths, generalized alphabets and an alternative native
index-zero count are outside this event.
