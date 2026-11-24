using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class DegreeTwoMomentWitnessDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/DegreeTwoMomentWitness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two integer spectra share their first-degree data and have different disjoint residual masses.",
        H("Identical first-degree data and different directed-gap energies"),
        Blocks(Describe.Lean(
            DescribeId.Create("equal-first-data-distinct-degree-two"),
            DeclarationHandle.Create(Owner + ".exists_equal_first_data_distinct_degree_two"),
            H("A five-point witness"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The spectra A and B have unit weights at the respective points "
                    + "(0,1,5,6,13) and (0,2,3,7,13). Both sums of the points are 25, "
                    + "both sums of the squares are 231, and both bands have endpoints 0 and 13.")),
                Paragraph(Text(
                    "For any resolution η from zero inclusive to one exclusive, only equal "
                    + "integer frequencies count as close. Thus the degree-one mass is five "
                    + "in each spectrum and all five pairs are diagonal. The directed-gap "
                    + "collision counts are 28 for A and 20 for B. The shared-endpoint "
                    + "correction subtracts 40 and adds 20 in each spectrum.")),
                Paragraph(Text(
                    "The arithmetic relation 0+6=1+5 accounts for all nonzero disjoint "
                    + "degree-two mass of A. The two pair orders and the two orders within "
                    + "each pair give total mass eight. B has zero disjoint mass at the "
                    + "same resolutions."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var r = new Formula.Subscript(F.Id("R"), D(2));
        return Disp(Seq(r, Open, a, Close, Sp, Eq, Sp, D(8), Comma, Sp,
            r, Open, b, Close, Sp, Eq, Sp, D(0)));
    }
}
