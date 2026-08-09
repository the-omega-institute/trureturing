using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class ZsqrtdImageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/ZsqrtdImage",
            "Doubled golden coordinates are exactly the Zsqrtd pairs with equal parity."),
        H("Image of Golden Coordinates"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("image-of-doubled-golden-coordinates"),
                H("Exact image criterion"),
                LeanTheorem("D5/S0/Carrier/ZsqrtdImage.mem_range_toZsqrtd_iff"),
                Disp(Seq(
                    Forall, Sp, F.Id("z"), InMacro, Operatorname, Grp(F.Id("Zsqrtd")),
                    Open, D(5), Close, Comma, Esc,
                    F.Id("z"), InMacro, Operatorname, Grp(F.Id("range")),
                    Open, Operatorname, Grp(F.Id("toZsqrtd")), Close,
                    Sp, Leftrightarrow, Sp,
                    Exists, Sp, F.Id("k"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("z"), Dot, F.Id("re"), Sp, Minus, Sp, F.Id("z"), Dot, F.Id("im"),
                    Sp, Eq, Sp, D(2), Sp, Times, Sp, F.Id("k"))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A quadratic integer lies in the image precisely when the difference of its two integer coordinates is even. The forward direction reads the golden real coordinate from that half-difference; the reverse direction reconstructs the unique preimage from the half-difference and the square-root coordinate.")))
            )),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Carrier/Ring"))]));
}
