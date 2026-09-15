# Clearing a candidate before dispatch

Four checks, in this order. The order is by cost, cheapest first, because every one of them can
kill a candidate on its own and the expensive ones are wasted if a cheap one would have.

Each check answers a different question. Passing three of four is what produced the discarded
lanes recorded below.

## 1. Is it still open? — one HTTP request

    curl -s "https://oeis.org/search?q=id:A048153&fmt=text"

Read the `%C`, `%F` and `%H` lines. A later comment asserting the conjecture is true, a formula
giving a closed form that implies it, or a link to a paper, each settle it.

**Do not use the `@[category research open]` annotation in google-deepmind/formal-conjectures as
evidence of openness.** It records that nobody edited that file. A048153 was marked open there
with the clone current to the day, while the OEIS entry had carried, since June 2026, a comment
that the conjecture is true with a *stronger* bound, a closed form involving class numbers of
imaginary quadratic orders, and a PARI implementation. The annotation lagged by three months.

`WebFetch` against `https://oeis.org/A...` returns HTTP 403; the `fmt=text` search endpoint
works.

Note who else is working this corpus. Tom Adamczewski, "OEIS Open: How many conjectures can
language models turn into theorems?", arXiv:2608.11941, builds a benchmark of 492 open OEIS
conjectures formalized in Lean from that same corpus and reports 147 resolved. OEIS entries now
carry comments like A211417's, recording that a conjecture "was proved by an autonomous AI
agent, see the Lean file", and A237271's, linking a Lean 4 proof dated August 2026.

## 2. Is the object already available? — grep, pinned Mathlib first

Ask what the statement *reduces to*, then search for that object rather than for the
identifier. Search pinned Mathlib before the repository: a general upstream theorem
instantiates silently and leaves no identifier trace anywhere.

Recorded misses, all of which reached or nearly reached a deposit:

- **A049473.** Its Beatty clause was absent from every path in the repository, whose own Beatty
  material is entirely golden-ratio. It is `Mathlib/NumberTheory/Rayleigh.lean`'s
  `compl_beattySeq` instantiated at the Hölder-conjugate pair `√2, 2+√2`.
- **A393856.** Parity clause, identifier absent everywhere relevant. Reduces to `B + B² = X`
  over `ZMod 2`, which `D5/S3/Arith/ArtinSchreierTracePowersOfTwo` already freezes under
  another entry's name.
- **A195194.** Same reduced object, closed by `SelfReferentialInverseSeriesParity`.
- **A396846.** Reduces to `f = X + f³` over `ZMod 3`, closed by
  `D5/S3/Arith/TernaryTraceSupport`: for any solution `f`, put `q = 1 − (f² + f·t + t²)`; then
  `q(f − t) = 0` and `q` is a unit, so `f = t`, with no induction.

### Read the source in full, and query the sequence itself

Two checks, in this order, both established by one case.

**Read the whole source section, not the statement of the conjecture.** A seat spent its run
reconstructing row 2 of the construction in arXiv:2503.19696 as the involution exchanging the two
Wythoff sequences. The paper says so itself, in the paragraph immediately after Proposition 5.6:
"The sequence q_n corresponds with sequence A002251 in Sloane's on-line encyclopedia of integer
sequences, obtained by swapping a(k) and b(k) for all k >= 1. This is evident from the expression
for q_n given in Lemma 5.5." The entire reconstruction was avoidable by reading four more
paragraphs of the paper that supplied the target.

**When the object is an integer sequence, query OEIS with the terms, not with words:**

    curl -s --get --data-urlencode "q=0 2 1 5 7 3 10 4 13 15 6 18 20 8" \
        --data-urlencode "fmt=text" https://oeis.org/search

That one query returns A002251 from the terms alone, with no shared vocabulary between the
recursion that generated them and the entry's definition. It is the check that would have caught
the same thing without reading the paper, which is why both are listed: the source may be silent,
but the catalogue is searchable from the object. The same query on row 3 returns nothing, which
is evidence that row 3 has not been catalogued — not evidence that it has no description.

OEIS is a library in the sense the standing goal means, and it was missing from this check:
Mathlib and the repository index were being searched while OEIS itself was not.

A path is not a statement. A module named for an object may prove something else about it;
treat a hit as "look here", not as "already done".

## 3. Which tier is it? — read the conjecture's provenance

A conjecture is a first-tier target when it is open because nobody has looked, not because it
is hard. Prize offers, named problems, and anything a specialist community is actively
attacking are out.

Shapes that look tractable and are not: A105020 is exactly binary Goldbach once the block is
reparameterised as `r(2n+2−r)`; A101779 implies infinitely many Sophie Germain primes;
A110835 is Sierpiński 1958; A005258's irreducibility claim sits on the Apéry numbers.

Also out: a conjecture whose asymptotic part is already published, leaving only a finite
residue. A111291 is covered for all large `x` by Zelinsky's 2002 Theorem 14; the inversion
bound of arXiv:1411.4092 Conjecture 2.7 is covered for large `b` coprime to 3 by Girstmair's
largest-values theorem, leaving a finite range and `3 ∣ b`.

## 4. Is the statement true? — minutes of computation

Compute the first instances from the **defining** objects, never from the conjectured pattern.
Reproducing the pattern from itself checks nothing.

This check is last because it is the most expensive and the least decisive: a statement can be
perfectly true and still fail all three checks above. A048153 held to n = 3000 and was already
proved; A049473 held to n = 300 and was Rayleigh instantiated.

## After dispatch

Judgement form (§3.2) is checked by a read-only review seat **before** the freeze, using
`templates/judgement-form-check-template.md`. Editing a `.lean` after `ledger-align` has written
the state pin collides with SL-008, so the only remedy is to discard the deposit and run the
whole chain again. One lane was lost that way before the stage existed.

### Read the entry's own settlement record before anything else

OEIS entries record their own settlement, in a later comment on the same entry. Run

    tools/scripts/agent/openproblem/oeis-conjecture-scan.py --ids A211417,A397356

and read what comes back. It reports two states and only two: a settlement marker with the line
that carries it, or no marker found. **No marker is not openness** — it is the absence of one
signal, and the scan says so rather than reporting the entry as open.

The case that established this: A211417 carries four integrality conjectures by Peter Bala dated
2025-08-28 and one settlement comment dated 2026-06-30. The settlement covers a different
statement — `(30n − 1) | a(n)`, proved by an autonomous agent whose Lean file the entry links —
and leaves Bala's four untouched. An entry with a proof link is not a settled entry; the marker
has to be read against the conjecture you intend to attack, one at a time.

The same entry shows why the scan cannot be trusted in the other direction either. Its links
include arXiv:2608.11941, which formalized 492 open OEIS conjectures and resolved 147 of them.
Anything in that resolved set is settled without any marker appearing in the entry text.
