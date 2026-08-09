using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenGapZeckendorfDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var criterion = Call("ofFn", Call("leastZeckendorfDigitTest", q));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Tower/GoldenGapZeckendorf",
                "Read each Fibonacci gap-word letter from the least Zeckendorf digit."),
            H("Golden Gap Word from Zeckendorf Digits"),
            Blocks(
                Paragraph(Text(
                    "For every valid position i, the letter is large exactly when index 2 is "
                    + "absent from wdigits i. The right side is inlined in both public theorems; "
                    + "this node does not define a second public word object.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("fibonacci-word-least-zeckendorf-digit"),
                    H("The Fibonacci word is the least-digit test"),
                    LeanTheorem(
                        "D5/S0/Tower/GoldenGapZeckendorf."
                        + "fibWord_eq_zeckendorf_word"),
                    Equal(Call("fibWord", q), criterion),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The least-digit table has the same two-step Fibonacci concatenation as "
                        + "fibWord. The upper block follows from Zeckendorf uniqueness after "
                        + "prefixing index Q+3, and the cases Q=0 and Q=1 are computed from the "
                        + "canonical representations of zero and one.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("golden-gap-word-least-zeckendorf-digit"),
                    H("The frozen gap word is the least-digit test"),
                    LeanTheorem(
                        "D5/S0/Tower/GoldenGapZeckendorf."
                        + "goldenGapWord_eq_zeckendorf_word"),
                    Equal(Call("goldenGapWord", q), criterion),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "This consequence rewrites only through the frozen "
                            + "golden_full_gap_word theorem, so the tower identification is a "
                            + "necessary proof dependency rather than a parallel derivation.")),
                        Paragraph(Text(
                            "Deferred: the explicit Beatty form, with a large letter exactly when "
                            + "floor((i+2)/phi)-floor((i+1)/phi)=1, is not proved in this S0 node. "
                            + "Its next admissible step is an S1 bridge from absence of digit 2 to "
                            + "goldenMechanicalLetter(i+1)=1; S0 does not import S1.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Conventions/WDigits")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenGapWord")),
            ]));
    }
}
