using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.CubicGain;

internal sealed class LiteralEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal normalized minors and fixed elimination matrices",
        H("Literal elimination in the original coordinates"),
        Blocks(
            Paragraph(Text("The source circuit is sourceJ, sourceN, sourceD, sourceC and sourceNumerator of SelectedRootCommonZero. Its three numerator entries are at clocks five, six and seven. sourceBt and sourceBb are the formal partial derivative numerators in the independent t,b coordinates. sourceE0 and sourceE1 are the ordered pairs (0,1) and (0,2). sourceE2 is the explicit integral polynomial for the ordered pair (1,2), with polynomial variable r and coefficient parameter b. All signs and the scale 45 use this order.")),
            Describe.Lean(DescribeId.Create("literal-third-minor-normalization"),
                DeclarationHandle.Create("D5/S3/Observer/CubicGain/LiteralElimination.source_e2_normalization"),
                H("The third division-free normalization"),
                StatementSource.FromAuthor(Normalization()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real t,b, the identity identifies 45 D(t,b) E2(tb,b) with b^7 times the original ordered derivative minor M12. No nonzero condition is imposed on b, D or a leading coefficient. The identity therefore includes b=0 and every zero of D. It does not define a pointwise quotient at those zeros."))), DescribeRole.Theorem),
            Paragraph(Text("The complete elimination identities additionally require the literal Sylvester determinants, their exact factorizations, positive primitive gcd normalization and coprimality. This normalization alone gives none of those conclusions, nor any exhaustion of real roots, original worlds or lifted sources.")))));

    private static Formula Call(string name, params Formula[] args) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Seq(args), Close);
    private static Formula Normalization()
    {
        var t = F.Id("t"); var b = F.Id("b");
        Formula B(string name, byte i) => Call(name, D(i), Comma, t, Comma, b);
        return Disp(Seq(Forall, Sp, t, Comma, b, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            D(4,5), Call("sourceD", t, Comma, b),
            Call("eval", Seq(F.Id("E"), Underscore, Grp(D(2)), Open, b, Close), Comma, t, b), Eq, Sp,
            b, Caret, Grp(D(7)), Open,
            B("sourceBt", 1), B("sourceBb", 2), Minus,
            B("sourceBb", 1), B("sourceBt", 2), Close));
    }
}
