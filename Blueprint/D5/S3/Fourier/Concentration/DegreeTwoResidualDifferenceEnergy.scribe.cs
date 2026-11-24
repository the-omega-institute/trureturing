using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DegreeTwoResidualDifferenceEnergyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DegreeTwoResidualDifferenceEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared endpoints give the correction from directed differences to disjoint two-term sums.",
        H("Disjoint two-term sums and directed differences"),
        Blocks(Describe.Lean(
            DescribeId.Create("degree-two-residual"),
            DeclarationHandle.Create(Owner + ".degree_two_residual"),
            H("Endpoint correction for the degree-two mass"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a finite index set with real frequencies g and real weights w. "
                    + "Take a nonnegative resolution η. The mass R with subscript two sums "
                    + "products of weighted multinomial coefficients over ordered pairs of "
                    + "degree-two count vectors with disjoint supports and frequency-sum "
                    + "discrepancy at most η.")),
                Paragraph(Text(
                    "Let A be the near-collision mass on the directed edges (i,j) with i≠j, "
                    + "using frequency g(i)−g(j), weight w(i)w(j), and resolution η. Let C "
                    + "with subscript i be the near-collision mass of the original spectrum "
                    + "with index i deleted, with the same resolution and including the diagonal.")),
                Paragraph(Text(
                    "Expanding each multinomial coefficient by its ordered words turns a pair "
                    + "of sums g(i)+g(k) and g(j)+g(l) into the two directed differences "
                    + "g(i)−g(j) and g(l)−g(k). Disjointness excludes the shared endpoints "
                    + "i=l and j=k in addition to the two forbidden loops. Subtract each "
                    + "shared-endpoint contribution and add their intersection once. At an "
                    + "intersection both directed edges are equal and their discrepancy is zero."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        var w = F.Id("w");
        var leftWeight = new Formula.Power(new Formula.Subscript(w, i), D(2));
        var rightWeight = new Formula.Power(new Formula.Subscript(w, j), D(2));
        var c = new Formula.Subscript(F.Id("C"), i);
        return Disp(Seq(new Formula.Subscript(F.Id("R"), D(2)), Sp, Eq, Sp, F.Id("A"),
            Sp, Minus, Sp, D(2), Sp, new Formula.Subscript(Sum, i), Sp, leftWeight, Sp, c,
            Sp, Plus, Sp, new Formula.Subscript(Sum, Seq(i, Comma, j, Sp, Neq, Sp, i)),
            Sp, leftWeight, Sp, rightWeight));
    }
}
