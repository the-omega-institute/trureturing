using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciGapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "The level-Q d-bonacci name values have exactly min(d,Q) adjacent lengths.",
            H("D-Bonacci Gaps"),
            Blocks(
                Paragraph(Text(
                    "A joint induction follows the finite run budget. A false prefix returns to "
                    + "full budget, a true prefix spends one unit, and the boundary between the "
                    + "two blocks is the scaled terminal gap of the full-budget layer.")),
                Describe.Lean(
                    DescribeId.Create("consecutive-d-bonacci-gap"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Gaps.consecutive_nameValue_gap"),
                    H("Consecutive d-bonacci gap"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Call("gapLabelExists", d, q, Id("i"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every consecutive difference is beta_d^-Q times the first f+1 "
                        + "reciprocal powers, for a label f in the interval [d-Q,d)."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("indexed-d-bonacci-values-increase-strictly"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Gaps.indexed_nameValue_strictMono"),
                    H("Indexed d-bonacci values increase strictly"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Call("StrictMono", Call("indexedNameValue", d, q))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every candidate is a positive power times a positive reciprocal-power "
                        + "sum, so positivity of adjacent steps yields strict monotonicity."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("exact-d-bonacci-gap-spectrum"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Gaps.adjacent_gap_spectrum"),
                    H("Exact d-bonacci gap spectrum"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Equal(
                                Call("adjacentGapSpectrum", d, q),
                                Call("gapLengthImage", Call("Ico", Add(d, Call("neg", q)), d)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "All adjacent gaps lie in the stated interval image. Conversely, each "
                        + "new endpoint label is realized at a prefix-block boundary and persists "
                        + "inside the zero-prefix block."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-gap-spectrum-cardinality"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Gaps.adjacent_gap_spectrum_card"),
                    H("D-bonacci gap spectrum cardinality"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Equal(
                                Call("card", Call("adjacentGapSpectrum", d, q)),
                                Call("min", d, q))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The reciprocal-prefix sums are strictly increasing in their labels. "
                        + "Thus the interval image has min(d,Q) distinct elements, and the full "
                        + "d-gap spectrum occurs exactly when d is at most Q."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Values")),
            ]));
    }
}
