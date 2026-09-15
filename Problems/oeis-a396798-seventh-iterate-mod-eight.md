---
slug: oeis-a396798-seventh-iterate-mod-eight
bibkey: hanna2026a396798
doi: null
url: https://oeis.org/A396798
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight
  - D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight
  - D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight
---

# The seventh compositional iterate of A396798 modulo eight

## Problem

Paul D. Hanna's OEIS A396798, revision 12, defines the ordinary generating
series by "G.f. satisfies A(x) = x + A^4(x)*A^5(x)." Its formula field says:

> G.f. A(x) = Sum_{n>=1} a(n)*x^n has the following properties, where A^n(x) denotes the n-th iteration of A(x).

The seventh comment states exactly:

> Conjecture: [x^n] A^7(x) == [7,1,3,5] repeating (mod 8) for n > 1.

Let I0(A)=X and I(k+1)(A)=Ik(A) composed with A. For the unique zero-constant
integer ordinary series satisfying A=X+I4(A)*I5(A), the result is:

```lean
forall n : Nat, 1 < n ->
  (8 : Int) ∣ PowerSeries.coeff n
    (CompositionalIterateCongruence.iterate
      IterateProductFourFiveEighthModEight.generatingSeries 7) -
    (if (n - 2) % 4 = 0 then (7 : Int)
     else if (n - 2) % 4 = 1 then 1
     else if (n - 2) % 4 = 2 then 3 else 5)
```

Every natural n>1 is included, with no upper bound or extra premise.
Residues 0,1,2,3 of (n-2)%4 select 7,1,3,5, starting at n=2. A^7 is
compositional iteration; products are ordinary multiplication, without
factorial normalization or convergence premises. The existing source is
`D5/S1/Recurrence/Residue/IterateProductFourFiveEighthModEight.generatingSeries`,
declaration identity
`sha256:ec9535ab3a9b0a1e907e9e393ae6d5cccfb485ff6209d712252354e4035bdfbc`.

## Motivation

This first-tier 2026 external named conjecture was preregistered in
[#7994](https://github.com/the-omega-institute/trureturing/issues/7994)
before seventh-clause proof or numerical probes. `question_answered` is
exactly the published seventh comment, using the third and fourth results
on the same source.

## Gap

The saved complete official JSON is revision 12, dated
2026-06-17T00:54:11-04:00, with SHA-256
`060572119a2cab42f21481cec1779aea1c1aaf9e0a576c1c9f283d6835348755`.
It was fetched with HTTP200; the live refresh returned HTTP403, so current
live-page freshness is unverified. The target remains that saved revision.

The complete source and direct references A396797/A396807/A396099/A213591
supply no seventh settlement in #7994's checked scope. Exact-A-number Crossref A396798 returned HTTP200
with 0 results. The broad seventh-iterate query's first 20 titles were
unrelated; this is not an exhaustive negative. arXiv returned HTTP429 and
was unavailable. The public Lean-code index returned 0 but omitted known
repository modules, so its zero is not absence evidence.

`dominating_theorem_search: not-found-in-searched-scope`. The third, fourth, fifth
and eighth results have different scopes; pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` supplies
general substitution and cast APIs, with no seventh-specific match in the
inspected scope. Unavailable sources give no negative evidence. Differently
named, differently indexed, unindexed or new proofs remain unexcluded;
no global priority is claimed.

## Route

Reduce the fixed integer source to F over ZMod8 and set U=I3(F). The source
definition gives its constant coefficient zero and linear coefficient one.
The existing `iterate_top` theorem compares F with X at degree two and
gives `coeff2(Ij(F))=j*coeff2(F)` for every natural j. The public third
result at n=2 gives `3*coeff2(F)=3`. Since 3*3=1 in ZMod8, coeff2(F)=1.
The public fourth tail and these low coefficients give `I4(F)=X+4X^2`.

Iteration preserves the zero constant and unit linear coefficients of U.
Its zero constant coefficient supplies `HasSubst U`; true iteration addition
at 4+3 and substitution give `I7(F)=U+4U^2`. The third period together with
coeff1(U)=1 yields `4*coeff_m(U)=4` for every m>0. In the convolution for
U^2 the endpoints vanish, and exactly n-1 positive-index pairs each contribute
four after weighting. Thus `4*coeff_n(U^2)=4*(n-1)` for every n>1.

The identity `n-1=4*((n-2)/4)+(n-2)%4+1` retains the natural-subtraction
bounds. Its four phase cases, combined with the third period, give 7,1,3,5.
Compatibility of coefficient reduction with compositional iteration and
the integer-cast divisibility equivalence give the stated integer theorem.

## Falsifier

A seventh-iterate coefficient at n>1 outside the selected residue modulo
eight would refute the assertion. A shifted phase, ordinary power, replaced
source or finite prefix changes the problem.

## Evidence

The single public result is
`D5/S1/Recurrence/Residue/IterateProductFourFiveSeventhModEight.result`.
Its direct result imports are the third and fourth modules. Their public
coefficient premises have these stored identities:

- `D5/S1/Recurrence/Residue/IterateProductFourFiveThirdModEight.result`:
  `sha256:c2cfc5988073cf06b3ff7bf1c89b243f4eb2348c493c0d9e3d4f8c32db736004`.
- `D5/S1/Recurrence/Residue/IterateProductFourFiveFourthModEight.result`:
  `sha256:14db1e606298fb3e83df375fad7441f5a170e171962ff81d2627c781cba442f7`.

The proof also uses accessible existing private generic declarations from
`DiagonalIterateEven` and `ThreeFourIterateProductModSix`. All new source,
low-coefficient, substitution, convolution and phase adaptations are local
to `result`; no helper theorem or replacement source is added.

## Triage

The result settles only the seventh comment under CLAUDE 3.2:
`proof_shape: bind-only`; `admission_basis: open-problem-resolution`;
`escape_witness: none`. Its unbounded symbolic argument has
`utility.kind: none`: it is neither bounded enumeration, a checker,
numerical reduction nor a certified finite instance.

The third, fourth, fifth and eighth comments have separate results.
Comments 2 and 6 remain with #6436 and the #6375 referral. The proposed
first-comment repair is separate from the original published claim; the
original contradiction remains non-kernel evidence. The whole entry is
not settled by this result.

## ASSUMED-UNVERIFIED

The proof does not establish current live-page freshness or completeness
of the bounded literature search. Differently indexed or unindexed proofs
remain unexcluded. No global priority or remaining-clause claim is made.
