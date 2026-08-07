using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenGapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Tower/GoldenGaps",
                "Sorted golden name values keep exactly two adjacent gap lengths from level two."),
            H("Golden Gaps"),
            Blocks(
                Paragraph(Text(
                    "The frozen Fibonacci-interval equivalence enumerates every level-Q golden "
                    + "name value in strictly increasing order. Consecutive differences of this "
                    + "enumeration are the tower's refinement gaps.")),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("indexed-golden-name-value"),
                    H("Indexed golden name value"),
                    LeanDefinition("D5/S0/Tower/GoldenGaps.indexedNameValue"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The nth name value under the frozen Fibonacci-interval equivalence, "
                        + "reusing the GoldenNames vocabulary as its single truth source.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("indexed-name-values-increase-strictly"),
                    H("Indexed name values increase strictly"),
                    LeanTheorem("D5/S0/Tower/GoldenGaps.indexed_nameValue_strictMono"),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("StrictMono", Call("indexedNameValue", q))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The enumeration lists name values in strictly increasing order, so "
                        + "adjacent differences are the geometric gaps of the level.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("consecutive-gaps-take-two-golden-powers"),
                    H("Consecutive gaps take two golden powers"),
                    LeanTheorem("D5/S0/Tower/GoldenGaps.consecutive_nameValue_gap"),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call(
                            "memberOf",
                            Call("gap", q, Id("i")),
                            Call(
                                "pairSet",
                                Call("goldenPow", Subtract(Num(0), q)),
                                Call("goldenPow", Subtract(Num(0), Add(q, Num(1))))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Every consecutive difference at level Q equals the golden ratio to the "
                        + "power minus Q or to the power minus Q minus one, by the two-branch "
                        + "structure of the Zeckendorf tail.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("adjacent-gap-spectrum-is-exactly-two-values"),
                    H("Adjacent gap spectrum is exactly two values"),
                    LeanTheorem("D5/S0/Tower/GoldenGaps.adjacent_gap_spectrum"),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("adjacentGapSpectrum", q),
                            Call(
                                "pairSet",
                                Call("goldenPow", Subtract(Num(0), q)),
                                Call("goldenPow", Subtract(Num(0), Add(q, Num(1))))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "From level two onward both gap lengths occur, so the adjacent-gap "
                        + "spectrum is exactly the two-element set of those golden powers; "
                        + "normalizing by the larger gap gives the two-type spectrum one and "
                        + "inverse golden ratio. Levels zero and one are degenerate with at "
                        + "most one gap, which is why the exact form assumes level at least two.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenNames")),
            ]));
    }

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
