using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class DoubleArtanhBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/DoubleArtanhBounds",
            "Bounds for the real inverse hyperbolic tangent on the open unit interval."),
        H("Double Artanh Bounds"),
        Blocks(
            DocumentBlock.Describe.Lemma(
                DescribeId.Create("double-artanh-bounds"),
                H("Double artanh bounds"),
                LeanTheorem("D5/S3/Quantum/DoubleArtanhBounds.double_artanh_bounds"),
                Disp(Seq(
                    Forall, Sp, F.Id("u"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma,
                    Quad, Sp, D(0), Lt, F.Id("u"), Lt, D(1), Sp, Rightarrow, Sp,
                    Frac, Grp(F.Id("u")), Grp(D(1), Plus, F.Id("u"), Caret, Grp(D(2))),
                    Sp, Le, Sp, Operatorname, Grp(F.Id("artanh")), Open, F.Id("u"), Close,
                    Sp, Le, Sp,
                    Frac, Grp(F.Id("u")), Grp(D(1), Minus, F.Id("u"), Caret, Grp(D(2))),
                    Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every real u strictly between zero and one, artanh(u) is at least "
                    + "u/(1+u^2) and at most u/(1-u^2). In Chapter 4's contraction-spectrum "
                    + "analysis, these inequalities serve as the lower- and upper-bound lemma "
                    + "for the double-artanh contraction metric.")))
            ))));
}
