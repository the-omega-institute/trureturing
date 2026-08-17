using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisot;

internal sealed class GapCountInstancesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula CountAt(long level) => Equal(
            Call("card", Call("beta13NormalizedGapSpectrum", Num(level))),
            Num(level));

        var prefix = Call(
            "append",
            Id("beta13GreedyDigits"),
            Call("singleton", Num(0)));
        var remainderAtTen = Equal(
            Call("getOptional", Id("beta13RemainderCodes"), Num(10)),
            Call("some", Call("pair", Num(21), Subtract(Num(0), Num(9)))));
        var eleventhDigitIsZero = Equal(
            Call(
                "floor",
                Multiply(
                    Id("beta13"),
                    Call(
                        "beta13GapCodeValue",
                        Call("pair", Num(21), Subtract(Num(0), Num(9)))))),
            Num(0));
        var frozenTestRejects = Equal(
            Call("beta13BelowGreedyPrefix", prefix),
            Id("false"));
        var frozenGeneratorOmits = new Formula.Not(new Formula.Relation(
            prefix,
            FormulaRelationOperator.MemberOf,
            Call("beta13Names", Num(11))));
        var modelBoundary = new Formula.Logic(
            remainderAtTen,
            FormulaLogicOperator.And,
            new Formula.Logic(
                eleventhDigitIsZero,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    frozenTestRejects,
                    FormulaLogicOperator.And,
                    frozenGeneratorOmits)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Three further finite beta13 gap counts are certified, and the frozen ten-digit "
                + "model is proved inadequate for an all-level theorem.",
            H("Further Non-Pisot Gap Count Instances"),
            Blocks(
                Paragraph(Text(
                    "These are individual finite computations at levels three, four, and five. "
                        + "They add evidence but do not state or prove a growth law.")),
                Describe.Lean(
                    DescribeId.Create("beta13-three-gap-types-at-level-three"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCountInstances."
                            + "beta13_normalized_gap_type_count_three"),
                    H("Three normalized gap types at level three"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(CountAt(3))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite internal adjacent-gap spectrum at Q = 3 has cardinality three."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("beta13-four-gap-types-at-level-four"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCountInstances."
                            + "beta13_normalized_gap_type_count_four"),
                    H("Four normalized gap types at level four"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(CountAt(4))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite internal adjacent-gap spectrum at Q = 4 has cardinality four."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("beta13-five-gap-types-at-level-five"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCountInstances."
                            + "beta13_normalized_gap_type_count_five"),
                    H("Five normalized gap types at level five"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(CountAt(5))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite internal adjacent-gap spectrum at Q = 5 has cardinality five."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("frozen-prefix-rejects-actual-eleven-digit-prefix"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCountInstances."
                            + "beta13_frozen_prefix_rejects_actual_eleven_digit_prefix"),
                    H("The frozen prefix model stops before the actual eleventh digit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(modelBoundary)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The exact remainder code after ten digits is (21,-9). Its next greedy "
                                + "digit is zero, but appending that digit to the frozen ten-digit "
                                + "list makes the current prefix predicate return false, so the "
                                + "current name generator omits the genuine eleven-digit prefix.")),
                        Paragraph(Text(
                            "Consequently the imported spectrum is a certified finite-prefix model, "
                                + "not a definition of the greedy beta-shift at arbitrary Q. An all-Q "
                                + "count theorem first requires an infinite greedy digit stream and a "
                                + "proof that its ordered adjacent-gap recursion adds exactly one new "
                                + "remainder type per level."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/NonPisot/GapCounts")),
            ]));
    }
}
