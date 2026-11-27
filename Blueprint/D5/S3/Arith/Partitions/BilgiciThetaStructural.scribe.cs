using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaStructuralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaStructural.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural quartic factorization.",
        H("Structural quartic factorization"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-structural-factorization"),
                DeclarationHandle.Create(Prefix + "structural_factorization"), H("The full weight component factors by the cubic"),
                StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The literal weight component lies in the joint kernel. Trace coefficients in degrees 30 "
                    + "and 49 recover the quotient class of its quartic cofactor from the projections of 6799 "
                    + "and 3689. The resulting polynomial is Q_str. The first trace coefficient is one in degree 30, so the cofactor has "
                    + "a nonzero class."))), DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Script(Formula symbol, Formula index) => Seq(symbol, Underscore, Grp(index));
    private static Formula Power(Formula symbol, Formula exponent) => Seq(symbol, Caret, Grp(exponent));
    private static Formula Z(Formula index) => Script(F.Id("Z"), index);
    private static Formula ThetaIdeal() => Script(Seq(Mathcal, Grp(F.Id("I"))), Theta);
    private static Formula Name(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula ResultFormula()
    {
        var q = F.Id("Q");
        var zero = D(0);
        var ring = Seq(Script(Seq(Mathbb, Grp(F.Id("F"))), D(1, 9)), OpenBracket,
            Z(D(1)), Comma, Dot, Dot, Dot, Comma, Z(D(9)), CloseBracket);
        var weightEleven = Script(Seq(OpenBracket, F.Id("B"), Power(F.Id("C"), D(3)),
            CloseBracket), D(1, 1));
        return Seq(Exists, Thin, q, InMacro, ring, Comma, Quad, Sp,
            q, Eq, Script(q, Grp(F.Id("str"))), Sp, Land, Sp,
            q, Neq, zero, Sp, Land, Sp,
            Name("Homogeneous"), Parenthesized(Seq(q, Comma, D(4))), Sp, Land, Sp,
            Name("WeightedHomogeneous"), Parenthesized(Seq(q, Comma, F.Id("w"), Comma, D(9))),
            Sp, Land, Sp, weightEleven, Minus, Script(F.Id("S"), F.Id("Z")), q,
            InMacro, ThetaIdeal(), Sp, Land, Sp, Overline, Grp(q), Neq, zero);
    }
}
