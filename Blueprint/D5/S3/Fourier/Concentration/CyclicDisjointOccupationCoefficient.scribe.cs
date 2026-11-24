using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicDisjointOccupationCoefficientDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicDisjointOccupationCoefficient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character projection retains the two occupation degrees and the cyclic frequency gap.",
        H("Cyclic frequency bands for disjoint occupations"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-disjoint-band-product"),
            DeclarationHandle.Create(Owner + ".cyclic_disjoint_band_product"),
            H("The mixed coefficient after character projection"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let q be positive. Each index j has a residue a(j) modulo q and a real "
                    + "weight w(j). For degree d and a set R of residues, M with subscript R is "
                    + "the weighted mass of ordered pairs of disjoint degree-d occupations "
                    + "whose first frequency sum minus the second belongs to R.")),
                Paragraph(Text(
                    "For character k, the local polynomial has constant coefficient one. "
                    + "For n from one to d, it assigns w(j)^n/n! to degree (n,0) with the "
                    + "negative character at n a(j), and to degree (0,n) with the positive "
                    + "character at n a(j). Write X with subscript k for the positive character. The product of those local polynomials is Q with "
                    + "subscript k. It has mixed coefficient Q(k)[d,d].")),
                Paragraph(Text(
                    "First expand a product in the additive monoid carrying the left degree, "
                    + "right degree and residue. The (d,d,r) coefficient groups all pairs "
                    + "with the two specified degrees and residue r. Multiplying by the square "
                    + "of d factorial gives the original multinomial weights. Applying a "
                    + "character to each residue commutes with convolution, leaving only "
                    + "the degree coordinates. Fourier inversion recovers the sum over R."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var d = F.Id("d");
        var k = F.Id("k");
        var r = F.Id("r");
        var q = F.Id("q");
        var band = F.Id("R");
        var mass = new Formula.Subscript(F.Id("M"), band);
        var c = new Formula.Subscript(F.Id("Q"), k);
        var coefficient = Seq(c, OpenBracket, d, Comma, d, CloseBracket);
        var character = new Formula.Subscript(F.Id("X"), k);
        return Disp(Seq(q, mass, Sp, Eq, Sp,
            new Formula.Power(Seq(Open, d, Bang, Close), D(2)), Sp,
            new Formula.Subscript(Sum, k), coefficient, Sp,
            new Formula.Subscript(Sum, Seq(r, Sp, InMacro, Sp, band)),
            character, Open, r, Close));
    }
}
