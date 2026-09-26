using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.PositivePairs.Span;

internal sealed class PositivePairsSpanLiteralPowerSubstitutionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal power substitution realizes actual positive pairs at controlled degree.",
        H("LiteralPowerSubstitution"),
        Blocks(
            Paragraph(Text(
                "The classical Lyndon bracket basis motivates the target directions. The new "
                + "content here is realizability by the complete family of actual recursively "
                + "generated positive-word pairs, without quotienting duplicate indices.")),
            D("literal-power-word", "literalPowerWord", "Literal letter-power substitution",
                "literalPowerWord m source replaces every letter of source by m consecutive copies of that same letter.", DescribeRole.Definition),
            D("literal-power-positive-pair", "literalPowerSubstitution_actual_positivePair", "Power substitution preserves lower data and scales the lead",
                "For finite A with decidable equality, m,r, and every actual pair index, powering both pair words multiplies each length by m, preserves equal positive lengths at levels r>=2 when m>0, preserves all scattered counts below r, and scales every degree-r count difference by m^r, including degenerate levels."))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(Statement(declaration))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string declaration)
    {
        var m = F.Id("m");
        var r = F.Id("r");
        var pattern = F.Id("pattern");
        var pair = Call("positivePairWords", r, F.Id("index"));
        var left = Call("left", pair);
        var right = Call("right", pair);
        var poweredLeft = Call("literalPowerWord", m, left);
        var poweredRight = Call("literalPowerWord", m, right);
        var countLeft = Call("scatteredCount", pattern, poweredLeft);
        var countRight = Call("scatteredCount", pattern, poweredRight);
        return declaration switch
        {
            "literalPowerWord" => Seq(Forall, Sp, m, Comma, F.Id("source"),
                Comma, Equal(Call("literalPowerWord", m, F.Id("source")),
                    Call("flatMap", F.Id("source"),
                        Call("lambda", F.Id("a"),
                            Call("replicate", m, F.Id("a")))))),
            "literalPowerSubstitution_actual_positivePair" => Seq(Forall, Sp,
                m, Comma, r, Comma, F.Id("index"), Comma, Sp,
                Equal(Call("length", poweredLeft), Multiply(Call("length", left), m)),
                Land, Equal(Call("length", poweredRight),
                    Multiply(Call("length", right), m)), Land, Open,
                F.D(2), Leq, Sp, r, Rightarrow,
                Equal(Call("length", poweredLeft), Call("length", poweredRight)),
                Close, Land, Open, F.D(0), Lt, Sp, m, Rightarrow,
                F.D(2), Leq, Sp, r, Rightarrow, Open,
                poweredLeft, Neq, Sp, F.Id("empty"), Land,
                Sp, poweredRight, Neq, Sp, F.Id("empty"), Close, Close, Land,
                Open, Forall, Sp, pattern, Comma, Call("length", pattern), Lt, Sp, r,
                Rightarrow, Equal(countLeft, countRight), Close, Land,
                Forall, Sp, pattern, Comma, Equal(Call("length", pattern), r),
                Rightarrow, Equal(Subtract(Call("castQ", countLeft),
                        Call("castQ", countRight)),
                    Multiply(Call("pow", Call("castQ", m), r),
                        Subtract(Call("castQ", Call("scatteredCount", pattern, left)),
                            Call("castQ", Call("scatteredCount", pattern, right)))))),
            _ => throw new ArgumentOutOfRangeException(nameof(declaration)),
        };
    }
}
