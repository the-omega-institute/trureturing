using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisot;

internal sealed class GapCountsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        Formula CountAt(long level, long count) => Equal(
            Call("card", Call("beta13NormalizedGapSpectrum", Num(level))),
            Num(count));

        var tribonacciCount = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(q, FormulaRelationOperator.GreaterThanOrEqual, Num(3)),
                FormulaLogicOperator.Implies,
                Equal(Call("card", Call("tribonacciAdjacentGapSpectrum", q)), Num(3))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The measured normalized gap spectra for beta13 have cardinalities six, eight, "
                + "and ten at levels six, eight, and ten, while the frozen Tribonacci count is three.",
            H("Measured Non-Pisot Gap Counts"),
            Blocks(
                Paragraph(Text(
                    "Names are finite greedy beta-shift words over digits zero, one, and two. "
                        + "Every suffix is compared with the certified greedy expansion prefix. "
                        + "The names remain in lexicographic order, their values are normalized "
                        + "by the common positive factor beta13^Q, and only internal adjacent "
                        + "differences are placed in the finite spectrum.")),
                Paragraph(Text(
                    "Exact pairs (a,b) represent a+b beta13. The three finite computations agree "
                        + "with the certified greedy-remainder spectra, and irrationality makes "
                        + "the passage from pair codes to real gap values injective.")),
                Describe.Lean(
                    DescribeId.Create("beta13-six-gap-types-at-level-six"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCounts."
                            + "beta13_normalized_gap_type_count_six"),
                    H("Six normalized gap types at level six"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(CountAt(6, 6))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite internal adjacent-gap spectrum at Q = 6 has cardinality six."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("beta13-eight-gap-types-at-level-eight"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCounts."
                            + "beta13_normalized_gap_type_count_eight"),
                    H("Eight normalized gap types at level eight"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(CountAt(8, 8))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite internal adjacent-gap spectrum at Q = 8 has cardinality eight."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("beta13-ten-gap-types-at-level-ten"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCounts."
                            + "beta13_normalized_gap_type_count_ten"),
                    H("Ten normalized gap types at level ten"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(CountAt(10, 10))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite internal adjacent-gap spectrum at Q = 10 has cardinality ten."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-gap-type-count-is-three"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/GapCounts."
                            + "tribonacci_normalized_gap_type_count"),
                    H("The frozen Tribonacci count is three"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(tribonacciCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is a fully qualified wrapper around the frozen Tribonacci "
                            + "adjacent-gap-spectrum cardinality theorem. Common positive "
                            + "normalization does not alter the number of gap types."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/NonPisot/Beta13")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Gaps")),
            ]));
    }
}
