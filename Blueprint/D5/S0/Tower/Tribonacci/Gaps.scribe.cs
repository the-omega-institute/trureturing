using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciGapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Sorted Tribonacci name values have exactly three adjacent lengths from level three.",
            H("Tribonacci Gaps"),
            Blocks(
                Paragraph(Text(
                    "A joint strong induction tracks both internal adjacent differences and the "
                    + "terminal distance to one. The three prefix blocks scale lower-level gaps "
                    + "by t^-1, t^-2, and t^-3, while both block boundaries scale terminal gaps.")),
                Describe.Lean(
                    DescribeId.Create("consecutive-tribonacci-three-gap-invariant"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Gaps.consecutive_nameValue_gap"),
                    H("Consecutive Tribonacci three-gap invariant"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("IsTribonacciGap", q,
                            Call("adjacentDifference", q, Id("i"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every consecutive difference is t^-Q, t^-(Q+1), or the sum of "
                        + "t^-(Q+1) and t^-(Q+2)."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("indexed-tribonacci-values-increase-strictly"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Gaps.indexed_nameValue_strictMono"),
                    H("Indexed Tribonacci values increase strictly"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("StrictMono", Call("indexedNameValue", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "All three possible differences are positive, so positivity of adjacent "
                        + "steps promotes to strict monotonicity on the complete finite interval."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-name-values-are-injective"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Gaps.tribonacciNameValue_injective"),
                    H("Tribonacci name values are injective"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("Injective", Call("tribonacciNameValue", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Strictness of the indexed values and bijectivity of the prefix "
                        + "enumeration separate every pair of admissible names."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("exact-tribonacci-three-gap-spectrum"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Gaps.adjacent_gap_spectrum"),
                    H("Exact Tribonacci three-gap spectrum"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("adjacentGapSpectrumCard", q))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The level-three witnesses persist in the zero-prefix block at every "
                        + "higher level, so all three candidate lengths occur. Their strict "
                        + "ordering also proves that the spectrum has cardinality three."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Values")),
            ]));
    }
}
