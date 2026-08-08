using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class DpiDefectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/DpiDefect",
            "Finite classical channels have a nonnegative Kullback-Leibler data-processing defect."),
        H("Nonnegativity of the Classical Data-Processing Defect"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-classical-data-processing-defect-is-nonnegative"),
                H("The classical data-processing defect is nonnegative"),
                LeanTheorem("D5/S3/Divergence/DpiDefect.dpi_defect_nonneg"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Nonempty")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")),
                    Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("p"), Open, F.Id("x"), Close, Eq, Sp, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Lt, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")),
                    F.Id("q"), Open, F.Id("x"), Close, Eq, Sp, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Lt, Sp,
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")),
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, Sp, D(1), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                    Minus,
                    F.Id("D"), Open,
                    F.Id("W"), F.Id("p"), Vert, Vert, Sp,
                    F.Id("W"), F.Id("q"), Close,
                    Geq, Sp, D(0), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let X and Y be finite alphabets, with X nonempty. Let p and q be " +
                        "strictly positive normalized real mass functions, and let W be a " +
                        "strictly positive row-stochastic channel. The divergence D and the " +
                        "output masses Wp and Wq are exactly the finite real-valued objects " +
                        "established by the preceding declarations.")),
                    Paragraph(Text(
                        "The chain identity rewrites the displayed defect as a finite sum over " +
                        "outputs. Each summand is the positive output mass (Wp)(y) multiplied by " +
                        "the divergence between the p- and q-posteriors at y. Those posteriors " +
                        "are normalized positive mass functions, so the established finite " +
                        "Gibbs inequality makes every posterior divergence nonnegative. Finite " +
                        "summation therefore proves the claim.")),
                    Paragraph(Text(
                        "This declaration records only nonnegativity. The existing zero-defect " +
                        "theorem supplies the separate posterior-equality characterization; no " +
                        "equality argument is repeated here.")))))));
}
