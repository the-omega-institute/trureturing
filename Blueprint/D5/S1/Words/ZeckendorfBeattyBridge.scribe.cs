using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ZeckendorfBeattyBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var i = Id("i");
        var q = Id("Q");
        var leastDigitAbsent = Call("leastDigitAbsent", i);
        var shiftedMechanicalOne = Call("goldenMechanicalLetterIsOne", Add(i, Num(1)));
        var floorWord = Call("ofFn", Call("shiftedGoldenBeattyFloorTest", q));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Words/ZeckendorfBeattyBridge",
                "Identify the least Zeckendorf digit with the shifted golden Beatty letter."),
            H("Zeckendorf-Beatty Bridge"),
            Blocks(
                Paragraph(Text(
                    "For a canonical Zeckendorf representation, the conjugate-power error lies "
                    + "on opposite sides of phi^(-3) according to whether index 2 is absent or "
                    + "present. This is exactly the existing golden mechanical window test.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("least-zeckendorf-digit-golden-mechanical-bridge"),
                    H("The least digit is the shifted mechanical letter"),
                    LeanTheorem(
                        "D5/S1/Words/ZeckendorfBeattyBridge.zeckendorf_beatty_bridge"),
                    Equal(leastDigitAbsent, shiftedMechanicalOne),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For every natural i, index 2 is absent from wdigits i if and only if "
                        + "goldenMechanicalLetter(i+1) equals one. The shift is part of the "
                        + "statement and is not absorbed into either frozen definition.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("fibonacci-word-explicit-golden-beatty-floor-test"),
                    H("The Fibonacci word has an explicit Beatty floor test"),
                    LeanTheorem(
                        "D5/S1/Words/ZeckendorfBeattyBridge.fibWord_eq_beatty_floor"),
                    Equal(Call("fibWord", q), floorWord),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "At each valid position i, the Boolean letter is true exactly when "
                        + "floor((i+2)/phi)-floor((i+1)/phi)=1. This follows by rewriting the "
                        + "frozen least-Zeckendorf-digit formula through the bridge above.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenGapZeckendorf")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S1/Words/GoldenMechanicalWord")),
            ]));
    }
}
