using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenGapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Sorted golden name values keep exactly two adjacent gap lengths from level two.",
            H("Golden Gaps"),
            Blocks(
                Paragraph(Text(
                    "The frozen Fibonacci-interval equivalence enumerates every level-Q golden "
                    + "name value in strictly increasing order. Consecutive differences of this "
                    + "enumeration are the tower's refinement gaps.")),
                Describe.Lean(
                    DescribeId.Create("indexed-golden-name-value"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGaps.indexedNameValue"),
                    H("Indexed golden name value"),
                    StatementSource.FromAuthor(FormulaDsl.Id("indexedNameValue")),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The nth name value under the frozen Fibonacci-interval equivalence, "
                        + "reusing the GoldenNames vocabulary as its single truth source."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("indexed-name-values-increase-strictly"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGaps.indexed_nameValue_strictMono"),
                    H("Indexed name values increase strictly"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("StrictMono", Call("indexedNameValue", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The enumeration lists name values in strictly increasing order, so "
                        + "adjacent differences are the geometric gaps of the level."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("consecutive-gaps-take-two-golden-powers"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGaps.consecutive_nameValue_gap"),
                    H("Consecutive gaps take two golden powers"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call(
                            "memberOf",
                            Call("gap", q, Id("i")),
                            Call(
                                "pairSet",
                                Call("goldenPow", Subtract(Num(0), q)),
                                Call("goldenPow", Subtract(Num(0), Add(q, Num(1)))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every consecutive difference at level Q equals the golden ratio to the "
                        + "power minus Q or to the power minus Q minus one, by the two-branch "
                        + "structure of the Zeckendorf tail."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("adjacent-gap-spectrum-is-exactly-two-values"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenGaps.adjacent_gap_spectrum"),
                    H("Adjacent gap spectrum is exactly two values"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("adjacentGapSpectrum", q),
                            Call(
                                "pairSet",
                                Call("goldenPow", Subtract(Num(0), q)),
                                Call("goldenPow", Subtract(Num(0), Add(q, Num(1)))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "From level two onward both gap lengths occur, so the adjacent-gap "
                        + "spectrum is exactly the two-element set of those golden powers; "
                        + "normalizing by the larger gap gives the two-type spectrum one and "
                        + "inverse golden ratio. Levels zero and one are degenerate with at "
                        + "most one gap, which is why the exact form assumes level at least two."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenNames")),
            ]));
    }
}
