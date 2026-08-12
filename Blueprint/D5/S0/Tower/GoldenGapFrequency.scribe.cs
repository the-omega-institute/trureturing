using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenGapFrequencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");
        var largeCount = Call("largeGapCount", q);
        var smallCount = Call("smallGapCount", q);

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Tower/GoldenGapFrequency",
                "Boundary-completed golden gaps have exact Fibonacci frequencies."),
            H("Golden Gap Frequency"),
            Blocks(
                Paragraph(Text(
                    "The frozen adjacent gaps are completed by the final interval from the last "
                    + "indexed name value to one. This keeps every counted gap attached to the "
                    + "actual GoldenName tower and includes the terminal refinement tail.")),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("boundary-completed-full-gap"),
                    H("Boundary-completed full gap"),
                    LeanDefinition("D5/S0/Tower/GoldenGapFrequency.fullGap"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "At an internal index this is the frozen consecutive name-value "
                        + "difference; at the final index it is the remaining interval to one.")))
                ),
                Describe.Lean(
                    DescribeId.Create("large-full-gap-count"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapFrequency.largeGapCount"),
                    H("Large full-gap count"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite number of boundary-completed gaps equal to the level-Q "
                        + "large golden length."))),
                    DescribeRole.Definition
                ),
                Describe.Lean(
                    DescribeId.Create("small-full-gap-count"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGapFrequency.smallGapCount"),
                    H("Small full-gap count"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite number of boundary-completed gaps equal to the level-Q "
                        + "small golden length."))),
                    DescribeRole.Definition
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("full-gap-counts-are-fibonacci"),
                    H("Full-gap counts are Fibonacci"),
                    LeanTheorem("D5/S0/Tower/GoldenGapFrequency.golden_full_gap_counts"),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Logic(
                            new Formula.Relation(
                                q,
                                FormulaRelationOperator.GreaterThanOrEqual,
                                Num(2)),
                            FormulaLogicOperator.Implies,
                            new Formula.Logic(
                                Equal(largeCount, Call("Fib", Add(q, Num(1)))),
                                FormulaLogicOperator.And,
                                new Formula.Logic(
                                    Equal(smallCount, Call("Fib", q)),
                                    FormulaLogicOperator.And,
                                    Equal(
                                        Add(largeCount, smallCount),
                                        Call("card", Call("GoldenName", q))))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "From level two onward the large and small multiplicities are Fib(Q+1) "
                        + "and Fib(Q). The proof uses the frozen golden gap substitution for the "
                        + "internal refinement partition, proves the terminal boundary recurrence, "
                        + "and checks that the two counts sum to the frozen GoldenName cardinality.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("large-to-small-gap-ratio-tends-to-golden-ratio"),
                    H("Large-to-small gap ratio tends to the golden ratio"),
                    LeanTheorem("D5/S0/Tower/GoldenGapFrequency.golden_gap_frequency_ratio"),
                    Equal(
                        Call(
                            "limitAtTop",
                            q,
                            new Formula.Fraction(
                                Call("largeGapCount", Add(q, Num(2))),
                                Call("smallGapCount", Add(q, Num(2))))),
                        Id("goldenRatio")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The exact count ratio is the shifted consecutive Fibonacci ratio, so "
                        + "the mathlib Fibonacci limit gives the golden ratio. This is an "
                        + "asymptotic frequency statement for tower gap types; it does not assert "
                        + "a champion classification, a pointwise Birkhoff theorem, or a global "
                        + "maximizing-orbit result. Those layers remain deferred.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenSubstitution")),
            ]));
    }

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
