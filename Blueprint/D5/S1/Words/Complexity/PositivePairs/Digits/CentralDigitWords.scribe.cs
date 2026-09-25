using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Digits;

internal sealed class PositivePairsDigitsCentralDigitWordsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Direction-major and scale-minor digits build literal positive words.",
        H("CentralDigitWords"),
        Blocks(
            Paragraph(Text(
                "This module defines the base-2^r digit arrays, literal powered blocks, complete "
                + "direction-major and scale-minor words, their all-zero reference word, and the "
                + "fixed base-length coefficient. These are repository constructions built from "
                + "the selected actual directions recorded by the preceding owner.")),
            D("digit-base", "digitBase", "Degree-dependent digit base",
                "digitBase r is 2^r.", DescribeRole.Definition),
            D("digit-array", "DigitArray", "Complete direction-scale digit arrays",
                "DigitArray A r t is the function space assigning a base-2^r digit to every selected actual direction and every scale below t.", DescribeRole.Definition),
            D("digit-value", "digitValue", "A direction's encoded natural",
                "digitValue reads the t digits of one direction in base digitBase r using Nat.ofDigits.", DescribeRole.Definition),
            D("digit-block", "digitBlock", "An actual positive-word digit block",
                "For a selected pair (u,v), scale s, and digit j, digitBlock concatenates j copies of the 2^s literal power of u and digitBase r-1-j copies of the matching power of v.", DescribeRole.Definition),
            D("multi-scale-word", "multiScaleWord", "The complete multi-scale positive word",
                "multiScaleWord concatenates every digitBlock in direction-major, scale-minor order; at t=0 the result is the empty word.", DescribeRole.Definition),
            D("reference-word", "referenceWord", "The zero-digit reference word",
                "referenceWord A r t is multiScaleWord at the all-zero digit array, hence uses the powered v-side in every block.", DescribeRole.Definition),
            D("base-length", "baseLength", "Common-length coefficient",
                "baseLength A r is (2^r-1) times the sum of the selected u-word lengths and is the fixed coefficient in the multi-scale length law.", DescribeRole.Definition))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration)
    {
        var r = F.Id("r");
        var t = F.Id("t");
        var direction = F.Id("direction");
        var scale = F.Id("scale");
        var digit = F.Id("digit");
        var digits = F.Id("digits");
        var count = Call("actualLyndonCount", F.Id("A"), r);
        var pair = Call("positivePairWords", r,
            Call("selectedDirection", r, direction));
        var poweredU = Call("literalPowerWord", Call("pow", Num(2), scale),
            Call("left", pair));
        var poweredV = Call("literalPowerWord", Call("pow", Num(2), scale),
            Call("right", pair));
        return declaration switch
        {
            "digitBase" => Seq(Forall, Sp, r, Comma,
                Equal(Call("digitBase", r), Call("pow", Num(2), r))),
            "DigitArray" => Seq(Forall, Sp, F.Id("A"), Comma, r, Comma, t,
                Comma, Equal(Call("DigitArray", F.Id("A"), r, t),
                    Call("functions", Call("Fin", count), Call("Fin", t),
                        Call("Fin", Call("digitBase", r))))),
            "digitValue" => Seq(Forall, Sp, r, Comma, t, Comma, digits,
                Comma, direction, Comma,
                Equal(Call("digitValue", r, t, digits, direction),
                    Call("NatOfDigits", Call("digitBase", r),
                        Call("ofFn", Call("Fin", t), Call("lambda", scale,
                            Call("nat", Call("apply", digits, direction, scale))))))),
            "digitBlock" => Seq(Forall, Sp, r, Comma, direction, Comma,
                scale, Comma, digit, Comma,
                Equal(Call("digitBlock", r, direction, scale, digit),
                    Call("append", Call("repeatedWord", digit, poweredU),
                        Call("repeatedWord", Subtract(Subtract(
                            Call("digitBase", r), Num(1)), digit), poweredV)))),
            "multiScaleWord" => Seq(Forall, Sp, r, Comma, t, Comma,
                digits, Comma,
                Equal(Call("multiScaleWord", r, t, digits),
                    Call("flatten", Call("ofFn", Call("Fin", count),
                        Call("lambda", direction,
                            Call("flatten", Call("ofFn", Call("Fin", t),
                                Call("lambda", scale, Call("digitBlock", r,
                                    direction, scale,
                                    Call("apply", digits, direction, scale)))))))))),
            "referenceWord" => Seq(Forall, Sp, r, Comma, t, Comma,
                Equal(Call("referenceWord", r, t),
                    Call("multiScaleWord", r, t,
                        Call("lambda", direction, Call("lambda", scale, Num(0)))))),
            "baseLength" => Seq(Forall, Sp, F.Id("A"), Comma, r, Comma,
                Equal(Call("baseLength", F.Id("A"), r),
                    Multiply(Subtract(Call("digitBase", r), Num(1)),
                        Call("sum", Call("Fin", count), Call("lambda", direction,
                            Call("length", Call("left", pair))))))),
            _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
        };
    }
}
