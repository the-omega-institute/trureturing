using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class DeficitIntegerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Deficit/DeficitInteger",
            "The normalized beta deficit of golden addition is an integer counting bottom carries."),
        H("The Normalized Beta Deficit Is an Integer Counting Bottom Carries"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-normalized-beta-deficit-is-an-integer-counting-bottom-carries"),
                H("The normalized beta deficit is an integer counting bottom carries"),
                LeanTheorem(
                    "D5/S1/Deficit/DeficitInteger.deficit_integer"),
                DeficitFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The model-set value of a natural number is obtained by evaluating its canonical "
                        + "Zeckendorf digits against golden-ratio powers, giving an element of the golden "
                        + "integers whose real image is the expansion face and whose Galois conjugate is the "
                        + "contraction face. The deficit of two operands is the failure of this value to be "
                        + "additive across their sum: the value of the first operand plus the value of the "
                        + "second minus the value of the sum. The theorem records three facts about this "
                        + "deficit at once. First, it is unchanged when read on the contraction face instead "
                        + "of the expansion face, because the two faces differ by a term proportional to the "
                        + "operand, and that proportional term cancels in the deficit exactly when the operands "
                        + "add. Second, the deficit is a rational integer rather than a general golden integer. "
                        + "Third, that integer is the signed count of the two bottom carry rules that fire while "
                        + "normalizing the concatenated digits, every internal carry contributing nothing.")),
                    Paragraph(Text(
                        "The proof runs the normalization as a chain of local value-preserving carries and "
                        + "tracks how the golden-integer evaluation moves at each step. The golden coordinate "
                        + "of the evaluation is exactly the represented natural number, and normalization "
                        + "preserves that number, so the deficit has vanishing golden coordinate; this is at "
                        + "once the identity of the two faces and the integrality, since a golden integer with "
                        + "vanishing golden coordinate is a rational integer and is fixed by conjugation. The "
                        + "remaining rational coordinate is accumulated one carry at a time. The two adjacent "
                        + "and higher repeated carries are exactly value-neutral, each a direct consequence of "
                        + "the golden fixed-point relation, while the two lowest repeated carries each hide a "
                        + "single unit of opposite sign. Summing these contributions along the deterministic "
                        + "normalization path expresses the deficit as the signed count of bottom carries.")))
            )),
[
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S0/Carrier/Conj")),
                        DocumentEdge.Dependency.Create(
                            GidRef.Create("D5/S1/Scale/Embedding")),
                    ]));

    private static Formula DeficitFormula()
    {
        Formula v1 = new Formula.Subscript(DefinitionDsl.Id("v"), Num(1));
        Formula v2 = new Formula.Subscript(DefinitionDsl.Id("v"), Num(2));
        Formula deficit = Call("c", v1, v2);
        Formula betaDeficit = Subtract(
            Add(Call("beta", v1), Call("beta", v2)),
            Call("beta", Add(v1, v2)));
        Formula carryDeficit = Subtract(Call("lowCarries"), Call("secondCarries"));
        return Disp(Seq(F.Id("c"), Open, F.Id("v"), Underscore, D(1), Comma, F.Id("v"), Underscore, D(2), Close, Sp, Colon, Eq, Sp, Beta, Open, F.Id("v"), Underscore, D(1), Close, Sp, Plus, Sp, Beta, Open, F.Id("v"), Underscore, D(2), Close, Sp, Minus, Sp, Beta, Open, F.Id("v"), Underscore, D(1), Plus, F.Id("v"), Underscore, D(2), Close, Sp, Eq, Sp, Beta, Apos, Open, F.Id("v"), Underscore, D(1), Close, Sp, Plus, Sp, Beta, Apos, Open, F.Id("v"), Underscore, D(2), Close, Sp, Minus, Sp, Beta, Apos, Open, F.Id("v"), Underscore, D(1), Plus, F.Id("v"), Underscore, D(2), Close, Comma, Sp, Quad, Sp, F.Id("c"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp, Quad, Sp, F.Id("c"), Sp, Eq, Sp, Operatorname, Grp(F.Id("lowCarries")), Sp, Minus, Sp, Operatorname, Grp(F.Id("secondCarries"))));
    }
}
