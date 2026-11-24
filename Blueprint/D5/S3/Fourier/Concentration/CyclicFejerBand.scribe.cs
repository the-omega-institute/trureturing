using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicFejerBandDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicFejerBand";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The overlap of two finite cyclic prefixes gives a positive Fourier weight for the band.",
        H("A cyclic Fejér bound for frequency bands"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-band-positive-fourier"),
            DeclarationHandle.Create(Owner + ".band_le_positive_fourier"),
            H("Cyclic band mass and the prefix character sum"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For the positive integer q, the band R_H consists of the residues of all "
                    + "integers from -H to H. The function M takes nonnegative real values. The "
                    + "transform uses the negative character. The window B_N(k) is the sum of the "
                    + "positive character at the residues of the first N natural-number indices.")),
                Paragraph(Text(
                    "For a band residue represented by an integer z, translate one coordinate "
                    + "of the pairs (j,j), with 0 ≤ j < N-H, by |z|. Use the first coordinate "
                    + "for positive z and the second for negative z. This injects N-H prefix "
                    + "indices into the fibre of ordered pairs with residue difference z. "
                    + "This count accommodates repeated residues when N exceeds q.")),
                Paragraph(Text(
                    "Summing fibrewise dominates (N-H) times the band mass by the pair sum. "
                    + "Fourier inversion expands the pair sum. Its two prefix sums are complex "
                    + "conjugates, so their product is the squared norm of B_N(k). The triangle "
                    + "inequality then gives the stated bound."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var q = F.Id("q");
        var h = F.Id("H");
        var n = F.Id("N");
        var k = F.Id("k");
        var r = F.Id("r");
        var m = F.Id("M");
        var integers = Seq(Mathbb, Grp(F.Id("Z")), Slash, q, Mathbb, Grp(F.Id("Z")));
        var band = new Formula.Subscript(F.Id("R"), h);
        var window = new Formula.Subscript(F.Id("B"), n);
        var windowValue = new Formula.Apply(window, [k]);
        var transformValue = new Formula.Apply(Seq(Widehat, Grp(m)), [k]);
        return Disp(new Formula.Aligned([
            Seq(Amp, Forall, Sp, q, Comma, h, Comma, n, Colon, Mathbb, Grp(F.Id("N")), Comma,
                Quad, Sp, q, Gt, D(0), Comma, Quad, Sp, h, Lt, n, Comma),
            Seq(Amp, Forall, Sp, m, Colon, integers, To, Sp,
                Mathbb, Grp(F.Id("R")), Underscore, Grp(Ge, D(0)), Comma),
            Seq(Amp, new Formula.Subscript(Sum, Seq(r, Sp, InMacro, Sp, band)), Sp, Call("M", r),
                Sp, Le, Sp, Frac, Grp(D(1)), Grp(q, Open, n, Minus, h, Close),
                new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, integers)), Sp,
                new Formula.Power(Seq(Bar, windowValue, Bar), D(2)), Bar, transformValue, Bar, Dot)
        ]));
    }
}
