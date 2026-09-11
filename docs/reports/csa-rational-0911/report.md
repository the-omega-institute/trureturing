# CSA rational history arithmetic batch

The guarded rational and exact-integer mathematics is unchanged. This report corrects its declaration, admission and dependency evidence. The complete CSA goal remains open beyond this batch, including rich reals and expression projection, concrete ZFC interpretation, definition elimination/conservativity, and model/relative-consistency obligations. The initial 15 propositions/117 ingested entries are not a completion denominator.

Current assessment of mathematical HEAD: `a20d0c3328a3c6f085105e6aeeab091449af819e`

Historical report-production HEAD: `9e1af55f012e7a4337886fce2cafdedf23f7e9a2`

Protected base: `02374e0e1c52b2751c9f214ad3884bb7e30bad50`

Full source authority: `df31b816bf570ddb71664473d1f7e33e8fcae6f0`

Raw Lean report: `sha256:7884fdbd82489e2c2f3531c4a0687e03b255f4cf89d28787c05a8970fcfc6fc2`

These are inherited source/report/Freeze bindings, not newly computed Freeze identities. The five source atoms identify Definition 9, Proposition 5, its proof and reduced-section paragraph, and the exact-division paragraph. Exact excerpts and atom IDs are in the audit's source-obligation catalog; that map is evidence about this scope, not a new coverage receipt.

## Preserved mathematical boundary

| Module | Freeze event | Module statement ID | Direct prerequisites |
|---|---|---|---|
| `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational` | `sha256:a5652d73a6fc22f4615ea439743a999b4ec4b6aa34cb1d1047e1781d0c7163fe` | `sha256:c45cae9d26070270d21ef8d449cea6d9f7282ba1960b048c1ddfc3b1885c115c` | `D5/S3/ConceptDynamics/Spacetime/ComplementFibers` (sha256:ba92a2b1cadfbbdfe0a59060b9b2f8ad4b85344e1f9ffb37632f828ad51ce842), `D5/S3/ConceptDynamics/Spacetime/GeneratedProduct` (sha256:0691566dcbcbca5cc9bd9cae7f776aa44a365db3d488832a8c3b3f84537fa420), `D5/S3/ConceptDynamics/Spacetime/ParallelComposition` (sha256:cd0bb50fbf9c8e122db2281ffdf7db91acba159ae7f6d1b5fe1e20ada8443ba6) |
| `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient` | `sha256:9642db999072b1e7f3e18bba74af7ce733fe6c386a2634b1d0887d6f89eceb4e` | `sha256:b46831adc4c934c701131bf05421e5bb2310d288c2d63e860c3db84ee139cedc` | `D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational` (sha256:c45cae9d26070270d21ef8d449cea6d9f7282ba1960b048c1ddfc3b1885c115c) |
| `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerExactDivision` | `sha256:0cc479a6ad712ea03cbc0279534d43fd6171222a8efa1f9d7efc3b095a664414` | `sha256:061d7df4a926bfe833ae6b1a82ae99bc2f5487e145ecee88e608d41e2ea79f8d` | `D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient` (sha256:b46831adc4c934c701131bf05421e5bb2310d288c2d63e860c3db84ee139cedc) |


The prerequisite-first build order is `RichRational`, `RationalQuotient`, `IntegerExactDivision`. In consumer-to-prerequisite notation, the module edges run `IntegerExactDivision → RationalQuotient → RichRational`, then to the listed frozen archive owners. The table lists module prerequisites, not every declaration's direct proof dependencies.

`RichRational.Fraction` contains two actual balanced histories and a nonzero denominator proof. Its exact `Rat` readout is integer-cast division. Cross multiplication is equivalent to equal readouts. Addition uses the ordered parallel composition of the cross-products; multiplication uses archive products; negation complements the actual numerator; inverse swaps the inputs under its numerator guard; division uses the source cross-products under the divisor-numerator guard. The dependent result constructors prove closure on those domains.

`RationalQuotient` forms the quotient of the full pair carrier by its numerical kernel. The section uses `Rat.num` and `Rat.den`, proves positive reduced coordinates and their uniqueness, and has the literal zero branch `0/1`. The integer embedding retains its supplied numerator history. The equivalence transports the field structure, and five class-operation laws establish agreement with the rich formulas. The field's total inverse convention at zero does not admit zero into the partial rich inverse or division domain.

`IntegerExactDivision` requires both a nonzero divisor and integer divisibility, selects the unique integer quotient, and returns its canonical balanced representative. The original unquotiented pair retains both input histories; its value and quotient class equal those of the canonical integer when exact division is legal. The quotient class itself does not retain those histories. General product-by-one families show that canonical selection can lose archive events, for every dimension and integer, including zero. The actual half pair refutes equality of the exact-integer and guarded-rational domains: that equality would require `2 ∣ 1`. Truncating and remainder division are outside this interface.

## Corrected declaration assessment

[declaration-audit.json](declaration-audit.json) and [declaration-shapes.md](declaration-shapes.md) account for all 90 included declarations against their unchanged proofs and existing statement IDs, type hashes and axiom closures. The 102 raw report entries contain 12 excluded equation/proof helpers, listed separately in the audit. Definitions, the structure and generated companions are not theorem proof-shape claims.

| Module | Bind-only theorems | Content theorems | Definitions | Structures | Generated companions | Included |
|---|---:|---:|---:|---:|---:|---:|
| RichRational | 20 | 0 | 11 | 1 | 17 | 49 |
| RationalQuotient | 14 | 0 | 6 | 0 | 0 | 20 |
| IntegerExactDivision | 15 | 1 | 5 | 0 | 0 | 21 |
| Total | 49 | 1 | 22 | 1 | 17 | 90 |

Twenty-two former content labels are withdrawn. Necessary source interfaces can be bind-only: `inv_readout` is exactly `(inv_div _ _).symm`; `reduced_coordinates_unique` applies `Rat.div_int_inj`; `rationalSection_rightInverse` rewrites frozen section readouts and applies `Rat.num_div_den`. `exactQuotient_spec` and `exactQuotient_unique` project `Classical.choose_spec`; their existence/uniqueness prerequisite extracts the divisibility witness and applies `mul_right_cancel₀`. These are bindings and projections, with no escape supplied by their usefulness.

Both general history-loss theorems are conservatively bind-only. `section_loses_product_history` rewrites the frozen product readout and archive/current cardinalities. A hypothetical equality yields `2*a = 2*a + 2 + 4*a`, with `a = natAbs n`, and `omega` normalizes the contradiction. `exactDivide_loses_product_history` identifies the exact quotient by uniqueness and applies that section result. No exact upstream theorem for the whole family is claimed, and neither family receives independent escape credit.

The sole content row is `division_domains_equal_refuted`. Its live concrete obstruction establishes the closed negation of `division_domains_equal_claim`, with `certified-instance`/`refutes` utility. That utility does not certify historical escape preregistration or supply admission credit to unrelated theorems.

## Source/API basis and direction of use

The current module assessment uses `rule-11-upstream-wrapper` for necessary source/API bindings. Each row names its exact obligation, owners and proof shape. This basis requires the necessary thin wrapper and an actual source/API obligation; it does not require a fabricated future consumer. Generated carrier declarations and definitional projection companions receive no independent admission credit. No row relies on `structural-consequence` as a catch-all or asserts `atom-required-bridge` without preregistration.

`RichRational` binds Definition 9 and Proposition 5 to the existing archive readouts and the exact fraction identities `div_eq_div_iff`, `div_add_div`, `div_mul_div_comm`, `neg_div`, `inv_div` and `div_div_div_eq`. Its guard and congruence interfaces are the required numerical-domain and replacement laws. `RationalQuotient` binds the required quotient and section to `Rat.num_div_den`, `Rat.div_int_inj`, `Setoid.quotientKerEquivOfRightInverse`, `Equiv.field` and `Equiv.ringEquiv`.

The actual operation consumers are `class_add → add_readout`, `class_mul → mul_readout`, `class_neg → neg_readout`, `class_inv → inv_readout` and `class_div → div_readout`, with each edge directed consumer → prerequisite. `rational_quotient_equiv → rationalSection_rightInverse` is the section edge; that equivalence does not consume all five rich-operation readout proofs. The audit separates these source-visible uses from compiler-captured constants.

The exact-division paragraph requires the divisibility/cancellation wrapper, its choice-specification and uniqueness interfaces, canonical output, equal fraction value and the history-loss boundary. Existing integer divisibility, `mul_right_cancel₀`, `Classical.choose_spec`, `div_eq_iff`, the canonical section, and archive cardinality identities are the named owners. In particular, `exactDivide_congr → exactQuotient_unique` and `exactDivide_congr → exactQuotient_spec` justify numerical replacement for the specified choice `i(k)`. There is no evidenced path to or from the half refutation. Its basis is the necessary unique-quotient/canonical-section API wrapper, not companion credit from that refutation. The universal history-loss rows bind the precise frozen cardinality and readout APIs to the source's explicit loss clause.

The retained q plans are historical proposals. Their RichReal, RealQuotient, ArithmeticExpression and SharedWorld consumer names are not live declarations in this report. This correction does not backdate a bridge preregistration, certify the historical first-Freeze sequence, or resolve the prior reject verdicts by fiat. No row-level source/API gap remains identified by this implementation assessment; eligibility and the corrected judgments remain for fresh independent review, including the disclosed historical preregistration limit for the refutation.

## Dependency evidence scope

The three unchanged `proof-edges-*.json` exports record historical `Expr.getUsedConstants` on elaborated value and type, with auxiliary expansion, **filtered to D5-owned constants**. `external_dependencies` means D5 declarations outside the current module. These lists omit Mathlib and Lean-core constants and do not certify a reduced live-proof closure or proof shape. `Rat.div_int_inj`, `Rat.num_div_den` and `inv_div` are absent despite actual source use. Their semantic owner citations are recorded separately in the authored audit; no compiler edge has been invented or added to the historical exports.

| Module | Included declarations | Captured edge rows | Missing capture |
|---|---:|---:|---|
| RichRational | 49 | 46 | `Fraction._sizeOf_inst`, `Fraction._sizeOf_1`, `Fraction.mk._flat_ctor` |
| RationalQuotient | 20 | 20 | None |
| IntegerExactDivision | 21 | 21 | None |

The three missing rows have explicit `missing-capture` status and `null` dependency arrays in the audit; the shapes table displays `missing`. Missing capture is not an empty dependency set. All captured arrays retain their historical contents. The inherited `direct_frozen_dependencies` field is repeated module prerequisite context; declaration-specific semantic citations carry exact existing D5 owner identities separately.

## Validation and provenance limits

The immutable raw report contains only `Classical.choice`, `Quot.sound` and `propext` in the target axiom closures. Current source bytes and report/Freeze identities bind the existing mathematics to the assessed HEAD. No Lean theorem, frozen event/state or digestion record is changed for this correction.

The authorized prior tests conclusion reports canonical focused Lean exit 0 and a meaningful boundary probe exit 0 on the unchanged mathematics. Its probe covered zero and negative inputs, exact source arithmetic examples, canonical quotient/section behavior, domain guards, history loss and the typed negation. The caller-supplied packet reports all three existing CI checks green on the starting HEAD. These are attributed verification evidence, not semantic approval. This documentation repair calls for canonical `make emit` and the existing Scribe/document checks; it does not justify a new mirrored test suite or repeating the passing full Lean/report/engineering builds.

The earlier report described successful `make deposit-uncovered` runs, `LEDGER_ALIGN` and freeze-last ordering. Those remain historical production claims, not actions or independently recertified lifecycle evidence of this repair. [search-receipts.json](search-receipts.json), the raw captured edges and retained historical plans preserve their bytes and original provenance. No new deposit, Freeze, coverage, commit, PR mutation or merge is established here.

Full CSA through the current source's Proposition 68 remains outside this batch's completion claim. Concrete ZFC coding/interpretation and definition elimination/conservativity are not discharged by using Lean types or the exact `Rat` field. No absolute `Con(ZFC)` claim follows. This is a corrected implementation assessment for a subsequent independent review, not review approval or whole-goal completion.
