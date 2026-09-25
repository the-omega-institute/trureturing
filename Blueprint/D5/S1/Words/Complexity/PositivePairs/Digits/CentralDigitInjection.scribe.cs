using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsCentralDigitInjectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multi-scale central digits are injective with exact length control.",
        H("CentralDigitInjection"),
        Blocks(
            Paragraph(Text(
                "This module combines the private central-coefficient identities with linear "
                + "independence of the selected actual directions. Its public theorem packages "
                + "lower-degree agreement, the exact degree-r coordinate formula, injectivity, "
                + "digit-array cardinality, nonempty equal-length pairs, and exact word length.")),
            D("actual-positive-pair-central-digits", "actual_positivePair_multiScale_central_digits", "Full central-digit system from actual pairs",
                "For finite linearly ordered A, r,t:N, and 2<=r, the selected actual leading differences are linearly independent; every selected pair has two nonempty equal-length words; every digit word agrees with referenceWord below degree r; each degree-r coefficient difference is the indicated sum of digitValue times actualLeadingDifference; the cutoffMagnus digit map is injective; the digit-array cardinality is (2^r)^(t*actualLyndonCount A r); and every digit word has length baseLength A r*(2^t-1)."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement())),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement()
    {
        var r = F.Id("r");
        var t = F.Id("t");
        var direction = F.Id("direction");
        var digits = F.Id("digits");
        var pattern = F.Id("pattern");
        var count = Call("actualLyndonCount", F.Id("A"), r);
        var selected = Call("selectedDirection", r, direction);
        var pair = Call("positivePairWords", r, selected);
        var left = Call("left", pair);
        var right = Call("right", pair);
        var word = Call("multiScaleWord", r, t, digits);
        var reference = Call("referenceWord", r, t);
        var leading = Call("actualLeadingDifference", r, selected);
        var lowerCount = Call("scatteredCount", pattern, word);
        var referenceCount = Call("scatteredCount", pattern, reference);
        var coefficientSum = Call("sum", Call("Fin", count),
            Call("lambda", direction,
                Multiply(Call("castQ", Call("digitValue", r, t, digits, direction)),
                    Call("coeff", leading, Call("ofList", pattern)))));
        return Seq(Forall, Sp, F.Id("A"), Comma, r, Comma, t, Comma,
            F.D(2), Leq, Sp, r, Rightarrow,
            Call("LinearIndependent", F.Id("Q"),
                Call("lambda", direction, leading)), Land,
            Open, Forall, Sp, direction, InMacro, Call("Fin", count), Comma,
            Open, left, Neq, Sp, F.Id("empty"), Land, Sp, right, Neq,
            Sp, F.Id("empty"), Land,
            Equal(Call("length", left), Call("length", right)), Close, Close, Land,
            Open, Forall, Sp, digits, Comma, pattern, Comma,
            Call("length", pattern), Lt, Sp, r, Rightarrow,
            Equal(lowerCount, referenceCount), Close, Land,
            Open, Forall, Sp, digits, Comma, pattern, Comma,
            Equal(Call("length", pattern), r), Rightarrow,
            Equal(Subtract(Call("castQ", lowerCount), Call("castQ", referenceCount)),
                coefficientSum), Close, Land,
            Call("Injective", Call("lambda", digits,
                Call("cutoffMagnus", r, word))), Land,
            Equal(Call("card", Call("DigitArray", F.Id("A"), r, t)),
                Call("pow", Call("digitBase", r), Multiply(t, count))), Land,
            Forall, Sp, digits, Comma,
            Equal(Call("length", word), Multiply(Call("baseLength", F.Id("A"), r),
                Subtract(Call("pow", Num(2), t), Num(1)))));
    }
}
