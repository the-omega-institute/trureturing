using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class HuangThreeColumnEnergyDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnEnergy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Energy rigidity for three signed Huang columns",
        H("Energy rigidity for three signed Huang columns"),
        Blocks(
            Paragraph(Text("Problem 2 of Hong, Wu and Xia asks whether the two-neighbor sensitivity of the nine-cube is 3 or 4. In the 18+3 fold, restrict the three minority Huang columns to their common set of empty rows. This energy test applies when each restricted column has exactly four retained neighbors. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("three-column-energy-definition"),
                DeclarationHandle.Create(Module + ".columnEnergy"),
                H("Squared energy on the retained rows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite subset of row indices, an integer array with three columns and an integer coefficient triple, sum the squares of the row values of the corresponding linear combination over the retained subset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-column-energy"),
                DeclarationHandle.Create(Module + ".three_column_energy"),
                H("Energy four characterizes the signed coordinate vectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume each Gram diagonal is four and each off-diagonal has absolute value at most one. Every nonzero integer coefficient triple has energy at least four. Equality holds exactly when one coefficient is 1 or −1 and the other two are zero. At least two nonzero coefficients force energy at least six.")),
                    Paragraph(Text("Expand the squares and bound each mixed term below by minus the sum of the two corresponding coefficient squares. With two active coefficients each square is charged once, leaving three times their sum. With three active coefficients each square is charged twice, leaving twice the sum. Nonzero integer squares are at least one. With one active coefficient the energy is exactly four times its square.")),
                    Paragraph(Text("Each retained Huang column has four entries equal to 1 or −1, giving diagonal four. The bound HuangThreeColumnIntegrality.common_neighbors_card_le_two gives at most two shared rows for distinct centers. With one shared row the Gram term is 1 or −1. With two, the centers and their two common neighbors form a square. The product of the four Huang edge signs is −1, so the two rowwise products are opposite and sum to zero. A fixed sign on a whole column multiplies both products by the same factor. The Gram bound uses the Huang square sign in this two-row case.")),
                    Paragraph(Text("For the fold application, write the retained-row equation as Bc = f with real coefficients. If 2^m f has even integer entries, apply HuangThreeColumnIntegrality.even_coefficients_of_three_cube_columns to 2^m c to obtain 2^m c = 2a for an integer triple a. Thus with s = 2/2^m the normalized source f/s is Ba. Under the four-entry Huang hypothesis, a nonzero normalized source of squared norm four must equal a signed retained column. A source of squared norm four that differs from all six signed columns rules out this conditional fold equation. The binary weight result HuangThreeColumnParity.cube_column_parity_weight concerns the reduction modulo two of the same normalized coefficients."))),
                DescribeRole.Theorem)),
        []));
}
