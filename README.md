trureturing — the last line of the ledger is always the first line of the next round.

<div align="center">

# trureturing

### **14,517 theorems, frozen.  One `sorry` — and it is not in the ledger.**

**A formal-mathematics repository that governs itself.**
Lean proves. A machine judges. Accepted truth is frozen, and never rewritten.

[![admission](https://github.com/the-omega-institute/trureturing/actions/workflows/ci.yml/badge.svg?branch=dev)](https://github.com/the-omega-institute/trureturing/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.31.0-2b2b2b)](lean-toolchain)
[![mathlib](https://img.shields.io/badge/mathlib-pinned-2b2b2b)](lake-manifest.json)
[![book](https://img.shields.io/badge/book-mdBook-2b2b2b)](https://the-omega-institute.github.io/trureturing-mdbook/)

</div>

---

## The mathematics

**trureturing formalizes the golden integer — the Zeckendorf coordinate system — in Lean 4.**
Every natural number is written in Fibonacci weights `1, 2, 3, 5, 8, …`; no two adjacent weights
may be occupied; and those canonical digits decode back to exactly one natural number. From that
single constraint the repository develops combinatorics, arithmetic, dynamics, spectra, and
analysis, and it carries each consequence all the way to a Lean proof.

The classical landmarks are closed, not cited. The **Three-Gap theorem** — that the first *N*
points of an irrational rotation cut the circle into arcs of at most three distinct lengths —
is proved in [`D5/S1/Phase/ThreeGap/`](D5/S1/Phase/ThreeGap/Main.lean) and sits in the frozen
ledger, with no `sorry`.

## Two hearts

The frontier is exactly two objects, and they are stated with deliberate asymmetry.

**O-5** is [`o5_independence`](D5/X_Frontier/Hearts.lean) — a `theorem` whose body is the single
`sorry` in this repository. It claims that the canonical golden Euler germ continues
meromorphically and that its analytic zeros in a declared band lie on the structural line.

**O-6** is `o6WeilPositivityStatement` — a `def … : Prop`. It **names** Weil positivity, which is
classically equivalent to the Riemann Hypothesis, and asserts no proof, no theorem, and no axiom.
A `sorry` count cannot see it. That is the point: the statement is fully bound — test class,
involution, convolution square, multiplicity-aware zero sum — so the summit has coordinates even
though no one has stood on it.

Weil's criterion runs both ways. If a zero lies off the line, some test function in that class
breaks positivity. Whichever way the Riemann Hypothesis falls, work against this statement
produces truth. That is why it was authorized.

## The ledger

Every module that passes admission is appended to `Golden/Frozen/accepted/`, and its address is a
Merkle hash over its module path, its statement, and the addresses of its prerequisites —
**change an ancestor and every descendant is readdressed.** The ledger only grows. Nothing is
revoked, nothing is re-attested, nothing is rewritten.

<table>
<tr><td><b>2,796</b></td><td>frozen modules, every event a <code>Freeze</code></td></tr>
<tr><td><b>14,517</b></td><td>theorems among <b>26,881</b> frozen declarations</td></tr>
<tr><td><b>407,857</b></td><td>lines of Lean under <code>D5/</code>, in 2,804 files</td></tr>
<tr><td><b>1</b></td><td><code>sorry</code> in the tree — outside the ledger, at the frontier</td></tr>
<tr><td><b>52</b></td><td>days from the first commit to this reading, across 17915 commits</td></tr>
</table>

*Measured 2026-09-01 on `dev`. The ledger advances by roughly two modules an hour, so these are a
dated snapshot, not a live counter.*

## It admits its own work

There is no human review gate anywhere in this repository, and that is a rule rather than an
accident: the constitution in [`CLAUDE.md`](CLAUDE.md) declares that **any gate producing
"requires human review" is by definition a harness bug.** Correctness is decided by the Lean
kernel and by three machine checks: `engineering`, `lean-inspect`, `admission`. Where a statement
is formally undecidable, the system marks it `open` and says so, rather than pretending. The two hearts are exactly that.

Enforcement on every GitHub merge is unverified; this repository checks its own gates, not
GitHub's configuration.

```text
docs/develop/theory/            reference input, never authority
        │  atomized into a content-addressed digestion ledger
        ▼
      D5/  ── Lean 4 ──────────  the only source of mathematical truth
        │
        │  judged by tools/ — a C# harness holding no mathematics of its own
        ▼
Golden/Frozen/accepted/         append-only; Merkle-addressed; never thawed
        │
        ▼
Blueprint/**/*.md  ─►  mdBook   derived projections, no authority
```

## Start here

```bash
make help          # every target this repository exposes
make test          # the mathematical gate
make preflight     # pre-verify the three CI checks locally
```

- [`agents/CONTEXT.md`](agents/CONTEXT.md) — the map, and the Route → Edit → Check workflow.
- [`CLAUDE.md`](CLAUDE.md) — the constitution every agent works under (Chinese).
- [`docs/develop/spec/golden-ledger-repo-spec.md`](docs/develop/spec/golden-ledger-repo-spec.md) — the specification.
- [`D5/`](D5/) — the Lean source. [`Blueprint/`](Blueprint/) — its narrative mirror; `.scribe.cs` is
  written by hand, `.md` is emitted from it.
- [`Problems/`](Problems/) — open problems, posted for outside attack.
