using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CommonResidualOccupationCoefficientDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CommonResidualOccupationCoefficient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A third polynomial degree records common occupation while character averaging selects the gap.",
        H("Cyclic occupation coefficients by common degree"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-residual-band"),
            DeclarationHandle.Create(Owner + ".common_residual_band"),
            H("A mixed coefficient for the common degree and frequency band"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a positive modulus q, a finite index set J, residues a(j), real "
                    + "weights w(j), total degree p, common degree h and a residue set R. "
                    + "The mass M with subscripts h and R counts ordered degree-p pairs "
                    + "having common degree h and signed gap in R, with multinomial weights.")),
                Paragraph(Text(
                    "In the local factor for j, two occupation counts u,v run from zero to p. "
                    + "Their term has degrees u,v,min(u,v), factorial coefficient "
                    + "w(j)^(u+v)/(u!v!) and the negative character at (u−v)a(j). "
                    + "Let Q with subscript k be the product of these local factors, and "
                    + "write X with subscript k for the positive character, for every k modulo q.")),
                Paragraph(Text(
                    "Coefficient selection in degrees (p,p,h) retains both totals and "
                    + "their common part. At the intermediate residue coefficient, a finite "
                    + "reindexing identifies the local coordinate choices with the pairs of "
                    + "occupation vectors. Fourier inversion applies the band filter. "
                    + "The case h=0 selects disjoint supports. At h=p the two vectors are "
                    + "equal and only the zero residue contributes."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var h = F.Id("h");
        var p = F.Id("p");
        var k = F.Id("k");
        var q = F.Id("q");
        var r = F.Id("r");
        var band = F.Id("R");
        var mass = new Formula.Subscript(F.Id("M"), Seq(h, Comma, band));
        var coefficient = Seq(new Formula.Subscript(F.Id("Q"), k), OpenBracket,
            p, Comma, p, Comma, h, CloseBracket);
        var character = new Formula.Subscript(F.Id("X"), k);
        return Disp(Seq(q, mass, Sp, Eq, Sp,
            new Formula.Power(Seq(Open, p, Bang, Close), D(2)), Sp,
            new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, Call("ZMod", q))), coefficient, Sp,
            new Formula.Subscript(Sum, Seq(r, Sp, InMacro, Sp, band)),
            character, Open, r, Close));
    }
}
