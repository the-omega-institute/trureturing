# CSA rational history arithmetic batch

This batch formalizes a guarded rational layer over balanced archive histories. It adds three Lean modules, their Blueprint mirrors, and three Freeze events. The batch is repository-derived mathematics; it is not a complete contextual spacetime arithmetic system, a ZFC conservativity theorem, a consistency proof, or a claim about `Con(ZFC)`.

Candidate HEAD: `9e1af55f012e7a4337886fce2cafdedf23f7e9a2`  
Protected base: `02374e0e1c52b2751c9f214ad3884bb7e30bad50`  
Raw Lean report: `sha256:7884fdbd82489e2c2f3531c4a0687e03b255f4cf89d28787c05a8970fcfc6fc2`

## Frozen modules

| Module | Freeze event | Module statement ID | Direct prerequisites |
|---|---|---|---|
| `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational` | `sha256:a5652d73a6fc22f4615ea439743a999b4ec4b6aa34cb1d1047e1781d0c7163fe` | `sha256:c45cae9d26070270d21ef8d449cea6d9f7282ba1960b048c1ddfc3b1885c115c` | `D5/S3/ConceptDynamics/Spacetime/ComplementFibers` (sha256:ba92a2b1cadfbbdfe0a59060b9b2f8ad4b85344e1f9ffb37632f828ad51ce842), `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct` (sha256:0691566dcbcbca5cc9bd9cae7f776aa44a365db3d488832a8c3b3f84537fa420), `D5/S3/ConceptDynamics/Spacetime/ParallelComposition` (sha256:cd0bb50fbf9c8e122db2281ffdf7db91acba159ae7f6d1b5fe1e20ada8443ba6) |
| `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient` | `sha256:9642db999072b1e7f3e18bba74af7ce733fe6c386a2634b1d0887d6f89eceb4e` | `sha256:b46831adc4c934c701131bf05421e5bb2310d288c2d63e860c3db84ee139cedc` | `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational` (sha256:c45cae9d26070270d21ef8d449cea6d9f7282ba1960b048c1ddfc3b1885c115c) |
| `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision` | `sha256:0cc479a6ad712ea03cbc0279534d43fd6171222a8efa1f9d7efc3b095a664414` | `sha256:061d7df4a926bfe833ae6b1a82ae99bc2f5487e145ecee88e608d41e2ea79f8d` | `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient` (sha256:b46831adc4c934c701131bf05421e5bb2310d288c2d63e860c3db84ee139cedc) |

The dependency order is `RichRational -> RationalQuotient -> IntegerExactDivision`. The first carrier keeps numerator and denominator histories and a nonzero denominator guard. `readout` projects a pair to `Rat`; cross multiplication is proved equivalent to equal projected readouts. Addition, multiplication, negation, guarded inverse, and guarded division preserve that projection.

`RationalQuotient` identifies the quotient of history pairs by the readout kernel with `Rat`, supplies a right-inverse section using reduced numerator/positive denominator coordinates, and transports the field operations. The field convention at zero is kept separate from the rich inverse/division guards.

`IntegerExactDivision` selects the unique integer quotient only under an explicit divisibility guard. It proves the projection and quotient compatibility statements, then records the concrete half pair: denominator readout `2`, numerator readout `1`, so the claimed equality of exact integer division and guarded rational division would require `2 ∣ 1`; `norm_num` refutes that. It also proves that canonical section retraction can lose the product's archived event history, making the projection loss explicit.

## Declaration accounting

`declaration-audit.json` contains all 90 declarations included in the three Freeze payloads, with exact statement IDs, type hashes, axiom closures, kernel dependency edges, direct prerequisite context, proof-shape assessment, escape witness, and admission basis. The three proof-edge files are generated from `Expr.getUsedConstants` on elaborated value and type expressions with auxiliary expansion.

`declaration-shapes.md` is the compact per-declaration view. `generated` rows are compiler or structure companions and carry no independent novelty claim. `content` rows are the guarded arithmetic or explicit counterexample statements; `bind-only` rows transport an established result through quotient/equivalence structure.

## Validation

Before each Freeze, the canonical `make deposit-uncovered` workflow ran against the immutable base. Both quotient and exact-division deposits exited 0 with `LEDGER_ALIGN ... added=1 ... conflicts=0`; header checks, Lean report generation, emission, values/FILEMAP/DAG checks all passed. The RichRational deposit was previously recorded with the same workflow and freeze-last ordering.

Search and capability receipts are in [search-receipts.json](search-receipts.json). The machine declaration and proof-edge evidence is in [declaration-audit.json](declaration-audit.json), [declaration-shapes.md](declaration-shapes.md), and the three `proof-edges-*.json` files.

## Limits

The formal result covers the current pinned Lean/mathlib environment and the listed carriers. It does not assert that every possible historical phase has a canonical inverse, that arbitrary observation maps preserve division, or that this arithmetic layer alone settles the remaining contextual spacetime, ZFC, or consistency questions.
